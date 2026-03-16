/* smb2fs.c - FUSE filesystem for SMB2 shares using libsmb2
 *
 * Usage: smb2fs <mountpoint> -o server=HOST,share=SHARE,user=USER[,password=PASS|passfd=FD|password_prompt][,domain=DOMAIN]
 *
 * Build on macOS with OSXFUSE:
 *   gcc -o smb2fs smb2fs.c \
 *       -I/usr/local/include/osxfuse -I/usr/local/include \
 *       -L/usr/local/lib -lsmb2 -losxfuse \
 *       -O2 \
 *       -D_FILE_OFFSET_BITS=64
 */

#define FUSE_USE_VERSION 26

#ifndef _FILE_OFFSET_BITS
#define _FILE_OFFSET_BITS 64
#endif

#include <stdint.h>
#include <stddef.h>
#include <sys/statvfs.h>
#include <fuse/fuse.h>
#include <fuse/fuse_opt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#include <poll.h>
#include <time.h>
#include <inttypes.h>

#include <smb2/smb2.h>
#include <smb2/libsmb2.h>
#include <smb2/libsmb2-raw.h>
#include <smb2/libsmb2-dcerpc.h>
#include <smb2/libsmb2-dcerpc-lsa.h>

/* ====================================================================
 * Main SMB2 context and config
 * ==================================================================== */

static struct smb2_context *smb2_ctx = NULL;

/* Best-effort wipe to reduce plaintext credential lifetime in memory. */
static void secure_zero(void *ptr, size_t len)
{
    volatile unsigned char *p = (volatile unsigned char *)ptr;
    while (len--) {
        *p++ = 0;
    }
}

/* Map libsmb2 NT status to POSIX errno for FUSE callback returns. */
static int smb2fs_errno(void)
{
    int nterr;
    int err;

    if (!smb2_ctx) {
        return -EIO;
    }
    nterr = smb2_get_nterror(smb2_ctx);
    if (!nterr) {
        return -EIO;
    }
    err = nterror_to_errno((uint32_t)nterr);
    if (err > 0) {
        return -err;
    }
    return -EIO;
}

struct smb2fs_config {
    char *server;
    char *share;
    char *user;
    char *password;
    char *domain;
    int   passfd;
    int   password_prompt;
};

static struct smb2fs_config cfg = { NULL, NULL, NULL, NULL, NULL, -1, 0 };

static void smb2fs_free_config(void)
{
    free(cfg.server);
    cfg.server = NULL;
    free(cfg.share);
    cfg.share = NULL;
    free(cfg.user);
    cfg.user = NULL;
    if (cfg.password) {
        secure_zero(cfg.password, strlen(cfg.password));
        free(cfg.password);
        cfg.password = NULL;
    }
    free(cfg.domain);
    cfg.domain = NULL;
    cfg.passfd = -1;
    cfg.password_prompt = 0;
}

static int smb2fs_password_from_fd(int fd, char **password_out)
{
    char chunk[256];
    char *buf = NULL;
    char *tmp;
    size_t len = 0;
    size_t cap = 0;
    size_t newcap;
    ssize_t nread;

    if (!password_out || fd < 0) {
        return -1;
    }

    while ((nread = read(fd, chunk, sizeof(chunk))) > 0) {
        if (len + (size_t)nread > 65536) {
            secure_zero(chunk, sizeof(chunk));
            free(buf);
            return -1;
        }
        if (len + (size_t)nread + 1 > cap) {
            newcap = cap ? cap : 256;
            while (newcap < len + (size_t)nread + 1) {
                newcap *= 2;
            }
            tmp = realloc(buf, newcap);
            if (!tmp) {
                if (buf) {
                    secure_zero(buf, len);
                    free(buf);
                }
                secure_zero(chunk, sizeof(chunk));
                return -1;
            }
            buf = tmp;
            cap = newcap;
        }
        memcpy(buf + len, chunk, (size_t)nread);
        len += (size_t)nread;
    }

    secure_zero(chunk, sizeof(chunk));

    if (nread < 0) {
        if (buf) {
            secure_zero(buf, len);
            free(buf);
        }
        return -1;
    }

    if (!buf) {
        buf = calloc(1, 1);
        if (!buf) {
            return -1;
        }
    } else {
        buf[len] = '\0';
    }

    while (len > 0 && (buf[len - 1] == '\n' || buf[len - 1] == '\r')) {
        buf[--len] = '\0';
    }

    *password_out = buf;
    return 0;
}

static int smb2fs_password_from_prompt(char **password_out)
{
    char *pw;
    char *copy;
    size_t len;

    if (!password_out) {
        return -1;
    }

    pw = getpass("SMB password: ");
    if (!pw) {
        return -1;
    }

    len = strlen(pw);
    copy = malloc(len + 1);
    if (!copy) {
        if (len) {
            secure_zero(pw, len);
        }
        return -1;
    }

    memcpy(copy, pw, len + 1);
    if (len) {
        secure_zero(pw, len);
    }
    *password_out = copy;
    return 0;
}

/* Overwrite password=... segments in argv to reduce command-line exposure. */
static void scrub_password_argv(struct fuse_args *args)
{
    int i;

    for (i = 0; i < args->argc; i++) {
        char *arg = args->argv[i];
        char *p;

        if (!arg) {
            continue;
        }

        p = strstr(arg, "password=");
        while (p) {
            p += strlen("password=");
            while (*p && *p != ',') {
                *p++ = 'x';
            }
            p = strstr(p, "password=");
        }
    }
}

static int smb2fs_is_smb_option_token(const char *opt)
{
    if (!opt) {
        return 0;
    }
    return (strncmp(opt, "server=", 7) == 0) ||
           (strncmp(opt, "share=", 6) == 0) ||
           (strncmp(opt, "user=", 5) == 0) ||
           (strncmp(opt, "password=", 9) == 0) ||
           (strncmp(opt, "domain=", 7) == 0) ||
           (strncmp(opt, "passfd=", 7) == 0) ||
           (strcmp(opt, "password_prompt") == 0);
}

/* Remove smb2fs-specific tokens from a comma-separated -o option list. */
static char *smb2fs_filter_mount_optlist(const char *optlist)
{
    char *in;
    char *out;
    char *tok;
    char *next;
    size_t out_len = 0;
    size_t max_len;
    int first = 1;

    if (!optlist) {
        return NULL;
    }

    max_len = strlen(optlist) + 1;
    in = strdup(optlist);
    out = malloc(max_len);
    if (!in || !out) {
        free(in);
        free(out);
        return NULL;
    }
    out[0] = '\0';

    tok = in;
    while (tok && *tok) {
        next = strchr(tok, ',');
        if (next) {
            *next = '\0';
            next++;
        }

        if (*tok != '\0' && !smb2fs_is_smb_option_token(tok)) {
            size_t tok_len = strlen(tok);
            if (!first) {
                out[out_len++] = ',';
            }
            memcpy(out + out_len, tok, tok_len);
            out_len += tok_len;
            out[out_len] = '\0';
            first = 0;
        }
        tok = next;
    }

    free(in);
    if (out_len == 0) {
        free(out);
        return NULL;
    }
    return out;
}

static int smb2fs_prepare_mount_args(struct fuse_args *src, struct fuse_args *dst)
{
    int i;

    if (!src || !dst || src->argc < 1 || !src->argv || !src->argv[0]) {
        return -1;
    }

    if (fuse_opt_add_arg(dst, src->argv[0]) < 0) {
        return -1;
    }

    for (i = 1; i < src->argc; i++) {
        const char *arg = src->argv[i];

        if (!arg) {
            continue;
        }

        if (strcmp(arg, "-o") == 0 && (i + 1) < src->argc) {
            char *filtered = smb2fs_filter_mount_optlist(src->argv[i + 1]);
            if (filtered) {
                if (fuse_opt_add_arg(dst, "-o") < 0 ||
                    fuse_opt_add_arg(dst, filtered) < 0) {
                    free(filtered);
                    return -1;
                }
                free(filtered);
            }
            i++;
            continue;
        }

        if (arg[0] == '-' && arg[1] == 'o' && arg[2] != '\0') {
            char *filtered = smb2fs_filter_mount_optlist(arg + 2);
            if (filtered) {
                if (fuse_opt_add_arg(dst, "-o") < 0 ||
                    fuse_opt_add_arg(dst, filtered) < 0) {
                    free(filtered);
                    return -1;
                }
                free(filtered);
            }
            continue;
        }

        if (smb2fs_is_smb_option_token(arg)) {
            continue;
        }

        if (fuse_opt_add_arg(dst, arg) < 0) {
            return -1;
        }
    }

    /* -s = single-threaded (libsmb2 is not thread-safe) */
    if (fuse_opt_add_arg(dst, "-s") < 0 ||
        fuse_opt_add_arg(dst, "-o") < 0 ||
        fuse_opt_add_arg(dst, "defer_permissions") < 0) {
        return -1;
    }
    return 0;
}

#define SMB2FS_OPT(t, p) { t, offsetof(struct smb2fs_config, p), 1 }

static struct fuse_opt smb2fs_opts[] = {
    SMB2FS_OPT("server=%s",   server),
    SMB2FS_OPT("share=%s",    share),
    SMB2FS_OPT("user=%s",     user),
    SMB2FS_OPT("password=%s", password),
    SMB2FS_OPT("passfd=%d",   passfd),
    SMB2FS_OPT("password_prompt", password_prompt),
    SMB2FS_OPT("domain=%s",   domain),
    FUSE_OPT_END
};

/* ====================================================================
 * SID cache and LSA / DCERPC state
 * ==================================================================== */

#define SID_CACHE_MAX  128
#define SID_UID_BASE   20000
#define SID_GID_BASE   50000

struct sid_cache_entry {
    char     sid_str[128]; /* "S-1-5-..." */
    char     name[256];    /* "DOMAIN\\username" (empty = lookup failed) */
    uint32_t id;           /* uid or gid */
};

static struct sid_cache_entry user_cache[SID_CACHE_MAX];
static int user_cache_n = 0;

static struct sid_cache_entry group_cache[SID_CACHE_MAX];
static int group_cache_n = 0;

/* IPC$/DCERPC/LSA state */
static struct smb2_context   *ipc_ctx = NULL;
static struct dcerpc_context *dce_ctx = NULL;
static struct ndr_context_handle lsa_ph;   /* LSA policy handle */
static int lsa_ok = 0;                     /* 1 once LSA is ready */

/* ====================================================================
 * Generic synchronous poll helper
 * ==================================================================== */

static int poll_smb2(struct smb2_context *ctx, int *done_flag, int timeout_s)
{
    struct pollfd pfd;
    time_t t = time(NULL);

    while (!*done_flag) {
        pfd.fd     = smb2_get_fd(ctx);
        pfd.events = smb2_which_events(ctx);
        if (poll(&pfd, 1, 1000) < 0)
            return -1;
        if (pfd.revents == 0) {
            if (time(NULL) - t > timeout_s)
                return -1;
            continue;
        }
        if (smb2_service(ctx, pfd.revents) < 0) {
            return -1;
        }
        if (time(NULL) - t > timeout_s)
            return -1;
    }
    return 0;
}

/* ====================================================================
 * SID → "S-1-5-..." string
 * ==================================================================== */

static void sid_to_str(const struct smb2_sid *s, char *buf, size_t len)
{
    uint64_t ia = 0;
    int i;
    char tmp[32];

    for (i = 0; i < 6; i++)
        ia = (ia << 8) | s->id_auth[i];

    snprintf(buf, len, "S-%u-%" PRIu64, (unsigned)s->revision, ia);
    for (i = 0; i < (int)s->sub_auth_count; i++) {
        snprintf(tmp, sizeof(tmp), "-%u", s->sub_auth[i]);
        strncat(buf, tmp, len - strlen(buf) - 1);
    }
}

/* ====================================================================
 * LSA initialisation  (called once before fuse_main)
 * ==================================================================== */

static void lsa_op_cb(struct dcerpc_context *dce, int status,
                      void *cmd_data, void *cb_data)
{
    struct lsa_openpolicy2_rep *rep = cmd_data;
    (void)cb_data;

    if (status == 0 && rep) {
        memcpy(&lsa_ph, &rep->PolicyHandle, sizeof(lsa_ph));
        lsa_ok = 1;
    }
    dcerpc_free_data(dce, rep);
}

static void lsa_co_cb(struct dcerpc_context *dce, int status,
                      void *cmd_data, void *cb_data)
{
    struct lsa_openpolicy2_req op_req;
    char *sysname;
    (void)cmd_data; (void)cb_data;

    if (status != 0)
        return;

    sysname = malloc(strlen(cfg.server) + 3);
    if (!sysname)
        return;

    memset(&op_req, 0, sizeof(op_req));
    sprintf(sysname, "\\\\%s", cfg.server);
    op_req.SystemName              = sysname;
    op_req.ObjectAttributes.Length = 24;
    op_req.DesiredAccess           = POLICY_LOOKUP_NAMES |
                                     POLICY_VIEW_LOCAL_INFORMATION;

    dcerpc_call_async(dce,
                      LSA_OPENPOLICY2,
                      lsa_OpenPolicy2_req_coder, &op_req,
                      lsa_OpenPolicy2_rep_coder,
                      sizeof(struct lsa_openpolicy2_rep),
                      lsa_op_cb, NULL);
    free(sysname);
}

static int init_lsa(void)
{
    ipc_ctx = smb2_init_context();
    if (!ipc_ctx)
        return -1;

    smb2_set_user(ipc_ctx, cfg.user);
    if (cfg.password) smb2_set_password(ipc_ctx, cfg.password);
    if (cfg.domain)   smb2_set_domain(ipc_ctx, cfg.domain);

    if (smb2_connect_share(ipc_ctx, cfg.server, "IPC$", cfg.user) < 0) {
        fprintf(stderr, "LSA: IPC$ connect failed: %s\n",
                smb2_get_error(ipc_ctx));
        smb2_destroy_context(ipc_ctx);
        ipc_ctx = NULL;
        return -1;
    }

    dce_ctx = dcerpc_create_context(ipc_ctx);
    if (!dce_ctx) {
        smb2_disconnect_share(ipc_ctx);
        smb2_destroy_context(ipc_ctx);
        ipc_ctx = NULL;
        return -1;
    }

    if (dcerpc_connect_context_async(dce_ctx, "lsarpc", &lsa_interface,
                                     lsa_co_cb, NULL) != 0) {
        dcerpc_destroy_context(dce_ctx);
        dce_ctx = NULL;
        smb2_disconnect_share(ipc_ctx);
        smb2_destroy_context(ipc_ctx);
        ipc_ctx = NULL;
        return -1;
    }

    /* Poll until OpenPolicy2 completes (lsa_ok becomes 1) */
    if (poll_smb2(ipc_ctx, &lsa_ok, 15) != 0 || !lsa_ok) {
        fprintf(stderr, "LSA: OpenPolicy2 timeout/failure\n");
        dcerpc_destroy_context(dce_ctx);
        dce_ctx = NULL;
        smb2_disconnect_share(ipc_ctx);
        smb2_destroy_context(ipc_ctx);
        ipc_ctx = NULL;
        return -1;
    }

    return 0;
}

/* ====================================================================
 * LSA LookupSids2 – synchronous wrapper for a single SID
 * ==================================================================== */

struct lsa_lookup_st {
    int  done;
    char name[256]; /* filled on success */
};

static void lsa_lookup_cb(struct dcerpc_context *dce, int status,
                           void *cmd_data, void *cb_data)
{
    struct lsa_lookup_st *s         = cb_data;
    struct lsa_lookupsids2_rep *rep = cmd_data;

    if (status == 0 && rep &&
        rep->TranslatedNames.Entries > 0 &&
        rep->TranslatedNames.Names[0].Name.utf8) {
        uint32_t    di    = rep->TranslatedNames.Names[0].DomainIndex;
        const char *uname = rep->TranslatedNames.Names[0].Name.utf8;
        const char *dname = (di < rep->ReferencedDomains.Entries) ?
                             rep->ReferencedDomains.Domains[di].Name.utf8 : NULL;
        if (dname)
            snprintf(s->name, sizeof(s->name), "%s\\%s", dname, uname);
        else
            strncpy(s->name, uname, sizeof(s->name) - 1);
    }
    dcerpc_free_data(dce, rep);
    s->done = 1;
}

static int lsa_lookup_one(const struct smb2_sid *sid,
                           char *name_out, size_t name_len)
{
    RPC_SID                    rpc;
    uint32_t                   sa[15];
    PRPC_SID                   psids[1];
    struct lsa_lookupsids2_req req;
    struct lsa_lookup_st       st;
    int i;

    if (!lsa_ok || !dce_ctx)
        return -1;

    rpc.Revision           = sid->revision;
    rpc.SubAuthorityCount  = sid->sub_auth_count;
    memcpy(rpc.IdentifierAuthority, sid->id_auth, 6);
    rpc.SubAuthority = sa;
    for (i = 0; i < (int)sid->sub_auth_count && i < 15; i++)
        sa[i] = sid->sub_auth[i];

    psids[0] = &rpc;

    memset(&req, 0, sizeof(req));
    memcpy(&req.PolicyHandle, &lsa_ph, sizeof(lsa_ph));
    req.SidEnumBuffer.Entries   = 1;
    req.SidEnumBuffer.SidInfo   = psids;
    req.TranslatedNames.Entries = 0;
    req.TranslatedNames.Names   = NULL;
    req.LookupLevel             = LsapLookupWksta;

    memset(&st, 0, sizeof(st));

    if (dcerpc_call_async(dce_ctx,
                          LSA_LOOKUPSIDS2,
                          lsa_LookupSids2_req_coder, &req,
                          lsa_LookupSids2_rep_coder,
                          sizeof(struct lsa_lookupsids2_rep),
                          lsa_lookup_cb, &st) != 0) {
        return -1;
    }

    if (poll_smb2(ipc_ctx, &st.done, 5) != 0 || st.name[0] == '\0')
        return -1;

    if (name_len == 0)
        return -1;
    strncpy(name_out, st.name, name_len - 1);
    name_out[name_len - 1] = '\0';
    return 0;
}

/* ====================================================================
 * SID → uid / gid  (with per-session cache, NO system() calls)
 * UIDs 10000-10127 are used for AD users, 10500-10627 for AD groups.
 * No local OS users are created; UID numbers appear in `ls -l` output.
 * ==================================================================== */

static uid_t sid_to_uid(const struct smb2_sid *sid)
{
    char  sid_str[128];
    char  name[256];
    uid_t uid;
    int   i;

    if (!sid)
        return getuid();

    sid_to_str(sid, sid_str, sizeof(sid_str));

    for (i = 0; i < user_cache_n; i++)
        if (strcmp(user_cache[i].sid_str, sid_str) == 0)
            return (uid_t)user_cache[i].id;

    if (user_cache_n >= SID_CACHE_MAX)
        return getuid();

    name[0] = '\0';
    lsa_lookup_one(sid, name, sizeof(name));   /* failure → name stays "" */

    {
        uint32_t rid = (sid->sub_auth_count > 0)
                       ? sid->sub_auth[sid->sub_auth_count - 1] : 0;
        uid = (name[0] != '\0') ? (uid_t)(SID_UID_BASE + (rid % 10000))
                                 : getuid();
    }

    strncpy(user_cache[user_cache_n].sid_str, sid_str,
            sizeof(user_cache[0].sid_str) - 1);
    strncpy(user_cache[user_cache_n].name, name,
            sizeof(user_cache[0].name) - 1);
    user_cache[user_cache_n].id = (uint32_t)uid;
    user_cache_n++;

    return uid;
}

static gid_t sid_to_gid(const struct smb2_sid *sid)
{
    char  sid_str[128];
    char  name[256];
    gid_t gid;
    int   i;

    if (!sid)
        return getgid();

    sid_to_str(sid, sid_str, sizeof(sid_str));

    for (i = 0; i < group_cache_n; i++)
        if (strcmp(group_cache[i].sid_str, sid_str) == 0)
            return (gid_t)group_cache[i].id;

    if (group_cache_n >= SID_CACHE_MAX)
        return getgid();

    name[0] = '\0';
    lsa_lookup_one(sid, name, sizeof(name));   /* failure → name stays "" */

    {
        uint32_t rid = (sid->sub_auth_count > 0)
                       ? sid->sub_auth[sid->sub_auth_count - 1] : 0;
        gid = (name[0] != '\0') ? (gid_t)(SID_GID_BASE + (rid % 10000))
                                 : getgid();
    }

    strncpy(group_cache[group_cache_n].sid_str, sid_str,
            sizeof(group_cache[0].sid_str) - 1);
    strncpy(group_cache[group_cache_n].name, name,
            sizeof(group_cache[0].name) - 1);
    group_cache[group_cache_n].id = (uint32_t)gid;
    group_cache_n++;

    return gid;
}

/* ====================================================================
 * Security descriptor query: compound CREATE + QUERY_INFO + CLOSE
 *
 * Uses HEAP-ALLOCATED callback state (like smb2-raw-getsd-async.c)
 * to avoid UAF when a timeout fires before all callbacks complete.
 * ==================================================================== */

struct sd_cb_data {
    smb2_command_cb              user_cb;
    void                        *user_cb_data;
    uint32_t                     status;
    struct smb2_security_descriptor *sd;
};

/* Final callback (called by close_cb): pass SD to caller */
static void sd_close_cb(struct smb2_context *smb2, int status,
                         void *cmd_data, void *cb_data)
{
    struct sd_cb_data *d = cb_data;
    (void)smb2; (void)cmd_data;

    if (d->status == SMB2_STATUS_SUCCESS)
        d->status = (uint32_t)status;

    /* Deliver result to user, then free our state */
    d->user_cb(smb2, -nterror_to_errno(d->status), d->sd, d->user_cb_data);
    free(d);
}

static void sd_qi_cb(struct smb2_context *smb2, int status,
                      void *cmd_data, void *cb_data)
{
    struct sd_cb_data        *d   = cb_data;
    struct smb2_query_info_reply *rep = cmd_data;
    (void)smb2;

    if (d->status == SMB2_STATUS_SUCCESS)
        d->status = (uint32_t)status;

    if (d->status == SMB2_STATUS_SUCCESS && rep)
        d->sd = (struct smb2_security_descriptor *)rep->output_buffer;
}

static void sd_create_cb(struct smb2_context *smb2, int status,
                          void *cmd_data, void *cb_data)
{
    struct sd_cb_data *d = cb_data;
    (void)smb2; (void)cmd_data;

    if (d->status == SMB2_STATUS_SUCCESS)
        d->status = (uint32_t)status;
}

/* Returns 0 on success; sd delivered via cb/cb_data */
static int send_sd_query(struct smb2_context *smb2, const char *path,
                          smb2_command_cb cb, void *cb_data)
{
    struct smb2_create_request     cr_req;
    struct smb2_query_info_request qi_req;
    struct smb2_close_request      cl_req;
    struct smb2_pdu               *pdu, *next_pdu;
    struct sd_cb_data             *d;

    d = malloc(sizeof(*d));
    if (!d)
        return -1;
    memset(d, 0, sizeof(*d));
    d->user_cb      = cb;
    d->user_cb_data = cb_data;

    /* CREATE */
    memset(&cr_req, 0, sizeof(cr_req));
    cr_req.requested_oplock_level = SMB2_OPLOCK_LEVEL_NONE;
    cr_req.impersonation_level    = SMB2_IMPERSONATION_IMPERSONATION;
    cr_req.desired_access         = SMB2_READ_CONTROL;
    cr_req.share_access           = SMB2_FILE_SHARE_READ |
                                    SMB2_FILE_SHARE_WRITE |
                                    SMB2_FILE_SHARE_DELETE;
    cr_req.create_disposition     = SMB2_FILE_OPEN;
    cr_req.name                   = path;

    pdu = smb2_cmd_create_async(smb2, &cr_req, sd_create_cb, d);
    if (!pdu) { free(d); return -1; }

    /* QUERY_INFO (security descriptor) */
    memset(&qi_req, 0, sizeof(qi_req));
    qi_req.info_type              = SMB2_0_INFO_SECURITY;
    qi_req.output_buffer_length   = 65535;
    qi_req.additional_information = SMB2_OWNER_SECURITY_INFORMATION |
                                    SMB2_GROUP_SECURITY_INFORMATION;
    memcpy(qi_req.file_id, compound_file_id, SMB2_FD_SIZE);

    next_pdu = smb2_cmd_query_info_async(smb2, &qi_req, sd_qi_cb, d);
    if (!next_pdu) { smb2_free_pdu(smb2, pdu); free(d); return -1; }
    smb2_add_compound_pdu(smb2, pdu, next_pdu);

    /* CLOSE */
    memset(&cl_req, 0, sizeof(cl_req));
    cl_req.flags = SMB2_CLOSE_FLAG_POSTQUERY_ATTRIB;
    memcpy(cl_req.file_id, compound_file_id, SMB2_FD_SIZE);

    next_pdu = smb2_cmd_close_async(smb2, &cl_req, sd_close_cb, d);
    if (!next_pdu) { smb2_free_pdu(smb2, pdu); free(d); return -1; }
    smb2_add_compound_pdu(smb2, pdu, next_pdu);

    smb2_queue_pdu(smb2, pdu);
    return 0;
}

/* Synchronous wrapper used from FUSE callbacks.
 * Heap-allocated so it survives even if the caller times out before
 * the compound-PDU callbacks fire. */
struct sd_sync_st {
    int                              is_finished;
    int                              caller_gave_up; /* set on timeout */
    int                              status;
    struct smb2_security_descriptor *sd;
};

static void sd_sync_cb(struct smb2_context *smb2, int status,
                        void *command_data, void *private_data)
{
    struct sd_sync_st *s = private_data;
    s->is_finished = 1;
    s->status      = status;
    s->sd          = command_data;  /* may be NULL on error */

    if (s->caller_gave_up) {
        /* Caller already returned from get_file_uid_gid; we own everything */
        if (s->sd)
            smb2_free_data(smb2, s->sd);
        free(s);
    }
}

static void get_file_uid_gid(const char *smb2_path,
                              uid_t *uid_out, gid_t *gid_out)
{
    struct sd_sync_st *st;
    int poll_rc;

    *uid_out = getuid();
    *gid_out = getgid();

    st = calloc(1, sizeof(*st));
    if (!st)
        return;

    if (send_sd_query(smb2_ctx, smb2_path, sd_sync_cb, st) != 0) {
        free(st);
        return;
    }

    poll_rc = poll_smb2(smb2_ctx, &st->is_finished, 10);

    if (poll_rc != 0 || !st->is_finished || st->status != 0) {
        if (st->is_finished) {
            if (st->sd)
                smb2_free_data(smb2_ctx, st->sd);
            free(st);
        } else {
            st->caller_gave_up = 1;
        }
        return;
    }

    if (st->sd) {
        if (st->sd->owner) {
            *uid_out = sid_to_uid(st->sd->owner);
        }
        if (st->sd->group) {
            *gid_out = sid_to_gid(st->sd->group);
        }
        smb2_free_data(smb2_ctx, st->sd);
    }
    free(st);
}

/* ====================================================================
 * Helper: smb2_stat_64 → struct stat
 * ==================================================================== */

static void smb2stat_to_stat(const struct smb2_stat_64 *s2, struct stat *st)
{
    memset(st, 0, sizeof(*st));
    if (s2->smb2_type == SMB2_TYPE_DIRECTORY) {
        st->st_mode  = S_IFDIR | 0755;
        st->st_nlink = 2;
    } else {
        st->st_mode  = S_IFREG | 0644;
        st->st_nlink = 1;
    }
    st->st_uid   = getuid();
    st->st_gid   = getgid();
    st->st_size  = (off_t)s2->smb2_size;
    st->st_atime = (time_t)s2->smb2_atime;
    st->st_mtime = (time_t)s2->smb2_mtime;
    st->st_ctime = (time_t)s2->smb2_ctime;
}

/* Strip leading '/' to get the SMB2-relative path */
static const char *smb2path(const char *fuse_path)
{
    if (fuse_path[0] == '/' && fuse_path[1] == '\0')
        return "";
    return fuse_path + 1;
}

/* ====================================================================
 * FUSE operations
 * ==================================================================== */

static int smb2fs_getattr(const char *path, struct stat *stbuf)
{
    struct smb2_stat_64 st;
    uid_t uid;
    gid_t gid;
    int   rc;

    if (strcmp(path, "/") == 0) {
        memset(stbuf, 0, sizeof(*stbuf));
        stbuf->st_mode  = S_IFDIR | 0755;
        stbuf->st_nlink = 2;
        stbuf->st_uid   = getuid();
        stbuf->st_gid   = getgid();
        return 0;
    }

    rc = smb2_stat(smb2_ctx, smb2path(path), &st);
    if (rc < 0)
        return smb2fs_errno();

    smb2stat_to_stat(&st, stbuf);

    if (lsa_ok) {
        get_file_uid_gid(smb2path(path), &uid, &gid);
        stbuf->st_uid = uid;
        stbuf->st_gid = gid;
    }

    return 0;
}

static int smb2fs_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
                          off_t offset, struct fuse_file_info *fi)
{
    struct smb2dir    *dir;
    struct smb2dirent *ent;

    (void)offset; (void)fi;

    dir = smb2_opendir(smb2_ctx, smb2path(path));
    if (dir == NULL)
        return smb2fs_errno();

    filler(buf, ".",  NULL, 0);
    filler(buf, "..", NULL, 0);

    while ((ent = smb2_readdir(smb2_ctx, dir)) != NULL) {
        struct stat st;
        smb2stat_to_stat(&ent->st, &st);
        filler(buf, ent->name, &st, 0);
    }

    smb2_closedir(smb2_ctx, dir);
    return 0;
}

static int smb2fs_open(const char *path, struct fuse_file_info *fi)
{
    int        flags = 0;
    struct smb2fh *fh;

    switch (fi->flags & O_ACCMODE) {
        case O_RDONLY: flags = O_RDONLY; break;
        case O_WRONLY: flags = O_WRONLY; break;
        default:       flags = O_RDWR;   break;
    }

    fh = smb2_open(smb2_ctx, smb2path(path), flags);
    if (fh == NULL)
        return smb2fs_errno();

    fi->fh = (uint64_t)(uintptr_t)fh;
    return 0;
}

static int smb2fs_create(const char *path, mode_t mode,
                          struct fuse_file_info *fi)
{
    struct smb2fh *fh;
    int flags;

    flags = fi ? (fi->flags & O_ACCMODE) : O_WRONLY;
    if (flags != O_RDONLY && flags != O_WRONLY && flags != O_RDWR) {
        flags = O_WRONLY;
    }
    if ((mode & 0222) == 0) {
        flags = O_RDONLY;
    }

    fh = smb2_open(smb2_ctx, smb2path(path),
                   O_CREAT | O_TRUNC | flags);
    if (fh == NULL)
        return smb2fs_errno();

    fi->fh = (uint64_t)(uintptr_t)fh;
    return 0;
}

static int smb2fs_read(const char *path, char *buf, size_t size,
                        off_t offset, struct fuse_file_info *fi)
{
    struct smb2fh *fh = (struct smb2fh *)(uintptr_t)fi->fh;
    int ret;
    (void)path;

    if (smb2_lseek(smb2_ctx, fh, offset, SEEK_SET, NULL) < 0)
        return smb2fs_errno();

    ret = smb2_read(smb2_ctx, fh, (uint8_t *)buf, size);
    return (ret < 0) ? smb2fs_errno() : ret;
}

static int smb2fs_write(const char *path, const char *buf, size_t size,
                         off_t offset, struct fuse_file_info *fi)
{
    struct smb2fh *fh = (struct smb2fh *)(uintptr_t)fi->fh;
    int ret;
    (void)path;

    if (smb2_lseek(smb2_ctx, fh, offset, SEEK_SET, NULL) < 0)
        return smb2fs_errno();

    ret = smb2_write(smb2_ctx, fh, (uint8_t *)buf, size);
    return (ret < 0) ? smb2fs_errno() : ret;
}

static int smb2fs_release(const char *path, struct fuse_file_info *fi)
{
    struct smb2fh *fh = (struct smb2fh *)(uintptr_t)fi->fh;
    (void)path;
    smb2_close(smb2_ctx, fh);
    return 0;
}

static int smb2fs_truncate(const char *path, off_t size)
{
    if (smb2_truncate(smb2_ctx, smb2path(path), (uint64_t)size) < 0)
        return smb2fs_errno();
    return 0;
}

static int smb2fs_unlink(const char *path)
{
    if (smb2_unlink(smb2_ctx, smb2path(path)) < 0)
        return smb2fs_errno();
    return 0;
}

static int smb2fs_mkdir(const char *path, mode_t mode)
{
    (void)mode;
    if (smb2_mkdir(smb2_ctx, smb2path(path)) < 0)
        return smb2fs_errno();
    return 0;
}

static int smb2fs_rmdir(const char *path)
{
    if (smb2_rmdir(smb2_ctx, smb2path(path)) < 0)
        return smb2fs_errno();
    return 0;
}

static int smb2fs_rename(const char *from, const char *to)
{
    if (smb2_rename(smb2_ctx, smb2path(from), smb2path(to)) < 0)
        return smb2fs_errno();
    return 0;
}

static int smb2fs_statfs(const char *path, struct statvfs *stv)
{
    struct smb2_statvfs s2stv;
    (void)path;

    if (smb2_statvfs(smb2_ctx, "", &s2stv) < 0)
        return smb2fs_errno();

    memset(stv, 0, sizeof(*stv));
    stv->f_bsize   = s2stv.f_bsize;
    stv->f_frsize  = s2stv.f_frsize;
    stv->f_blocks  = s2stv.f_blocks;
    stv->f_bfree   = s2stv.f_bfree;
    stv->f_bavail  = s2stv.f_bavail;
    stv->f_namemax = s2stv.f_namemax;
    return 0;
}

static struct fuse_operations smb2fs_ops = {
    .getattr  = smb2fs_getattr,
    .readdir  = smb2fs_readdir,
    .open     = smb2fs_open,
    .create   = smb2fs_create,
    .read     = smb2fs_read,
    .write    = smb2fs_write,
    .release  = smb2fs_release,
    .truncate = smb2fs_truncate,
    .unlink   = smb2fs_unlink,
    .mkdir    = smb2fs_mkdir,
    .rmdir    = smb2fs_rmdir,
    .rename   = smb2fs_rename,
    .statfs   = smb2fs_statfs,
};

/* ====================================================================
 * main
 * ==================================================================== */

int main(int argc, char *argv[])
{
    struct fuse_args raw_args = FUSE_ARGS_INIT(argc, argv);
    struct fuse_args args = FUSE_ARGS_INIT(argc, argv);
    struct fuse_args mount_args = FUSE_ARGS_INIT(0, NULL);
    int ret = 1;
    int pw_sources = 0;
    char *runtime_password = NULL;

    if (fuse_opt_parse(&args, &cfg, smb2fs_opts, NULL) < 0) {
        fuse_opt_free_args(&args);
        smb2fs_free_config();
        return 1;
    }
    scrub_password_argv(&args);
    scrub_password_argv(&raw_args);

    if (!cfg.server || !cfg.share || !cfg.user) {
        fprintf(stderr,
            "Usage: %s <mountpoint> -o server=HOST,share=SHARE,"
            "user=USER[,password=PASS|passfd=FD|password_prompt][,domain=DOMAIN]\n",
            argv[0]);
        goto out;
    }

    if (cfg.password) {
        pw_sources++;
    }
    if (cfg.passfd >= 0) {
        pw_sources++;
    }
    if (cfg.password_prompt) {
        pw_sources++;
    }
    if (pw_sources > 1) {
        fprintf(stderr,
                "Choose only one password source: password=, passfd=, or "
                "password_prompt\n");
        goto out;
    }
    if (cfg.passfd >= 0) {
        if (smb2fs_password_from_fd(cfg.passfd, &runtime_password) != 0) {
            fprintf(stderr, "Failed to read password from passfd=%d\n",
                    cfg.passfd);
            goto out;
        }
        cfg.password = runtime_password;
    } else if (cfg.password_prompt) {
        if (smb2fs_password_from_prompt(&runtime_password) != 0) {
            fprintf(stderr, "Failed to read password from prompt\n");
            goto out;
        }
        cfg.password = runtime_password;
    }

    /* Connect main share */
    smb2_ctx = smb2_init_context();
    if (!smb2_ctx) {
        fprintf(stderr, "Failed to init smb2 context\n");
        goto out;
    }

    smb2_set_user(smb2_ctx, cfg.user);
    if (cfg.password) smb2_set_password(smb2_ctx, cfg.password);
    if (cfg.domain)   smb2_set_domain(smb2_ctx, cfg.domain);

    if (smb2_connect_share(smb2_ctx, cfg.server, cfg.share, cfg.user) < 0) {
        fprintf(stderr, "Connect failed: %s\n", smb2_get_error(smb2_ctx));
        smb2_destroy_context(smb2_ctx);
        smb2_ctx = NULL;
        goto out;
    }

    /* Try to initialise LSA for SID -> name resolution (non-fatal). */
    if (init_lsa() != 0) {
        fprintf(stderr,
                "smb2fs: warning: LSA init failed - owner/group will show as "
                "current user\n");
    }

    /* Authentication complete - clear parsed plaintext password. */
    if (cfg.password) {
        secure_zero(cfg.password, strlen(cfg.password));
        free(cfg.password);
        cfg.password = NULL;
    }

    fflush(stderr);

    if (smb2fs_prepare_mount_args(&raw_args, &mount_args) < 0) {
        fprintf(stderr, "Failed to prepare FUSE arguments\n");
        smb2_disconnect_share(smb2_ctx);
        smb2_destroy_context(smb2_ctx);
        smb2_ctx = NULL;
        goto out;
    }

    ret = fuse_main(mount_args.argc, mount_args.argv, &smb2fs_ops, NULL);

    /* Cleanup */
    if (dce_ctx) {
        dcerpc_destroy_context(dce_ctx);
        dce_ctx = NULL;
    }
    if (ipc_ctx) {
        smb2_disconnect_share(ipc_ctx);
        smb2_destroy_context(ipc_ctx);
        ipc_ctx = NULL;
    }
    smb2_disconnect_share(smb2_ctx);
    smb2_destroy_context(smb2_ctx);
    smb2_ctx = NULL;

out:
    fuse_opt_free_args(&mount_args);
    fuse_opt_free_args(&args);
    smb2fs_free_config();
    return ret;
}
