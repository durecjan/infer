#include <stdlib.h>

/* Inspired by OpenSSL's SSL_CTX_new pattern.
   Allocates a context struct with two owned buffers;
   cascading cleanup frees earlier allocations on failure. */

struct conn_ctx {
    char *hostname;
    char *cert_buf;
    char *session_id;
};

struct conn_ctx *conn_ctx_new(int host_len, int cert_len) {
    struct conn_ctx *ctx = (struct conn_ctx *)malloc(sizeof(struct conn_ctx));
    if (ctx == NULL) return NULL;

    ctx->hostname = (char *)malloc(host_len);
    if (ctx->hostname == NULL) {
        free(ctx);
        return NULL;
    }

    ctx->cert_buf = (char *)malloc(cert_len);
    if (ctx->cert_buf == NULL) {
        free(ctx->hostname);
        free(ctx);
        return NULL;
    }

    ctx->session_id = NULL;
    return ctx;
}

/*
 * CASE ctx == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * (ctx==null) & (Base(ctx)==0) & (End(ctx)==0) & (%ret==null) & (Base(%ret)==0) & (End(%ret)==0)
 *
 * CASE ctx->hostname == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * Freed(ctx) & (y1==null) & (Base(y1)==0) & (End(y1)==0 &) (%ret==null) & (Base(%ret)==0) & (End(%ret)==0)
 *
 * CASE ctx->cert_buf == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * Freed(ctx) & Freed(y1) & (y2==null) & (Base(y2)==0) & (End(y2)==0) & (%ret==null) & (Base(%ret)==0) & (End(%ret)==0)
 *
 * CASE ctx->cert_buf != NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * (ctx+0) -(8)-> (y1) * (ctx+8) -(8)-> (y2) * (ctx+16) -(8)-> (y3) * (y1+0) -(host_len)-> block * (y2+0) -(cert_len)-> block
 * (Base(ctx)==ctx+0) & (End(ctx)==ctx+24) & (Base(y1)==y1+0) & (End(y1)==y1+host_len) & (Base(y2)==y2+0) & (End(y2)==y2+cert_len) & (y3==null) & (Base(y3)==0) & (End(y3)==0) & (%ret==ctx)
 *
 * Expected error contracts:
 * <empty>
 */
