#include <stdlib.h>

/* Inspired by OpenSSL's BUF_MEM_new / BUF_MEM_grow pattern.
   Allocates a buffer struct with an owned data region;
   cleans up the struct if data allocation fails. */

struct buf_mem {
    long length;
    char *data;
    long max;
};

struct buf_mem *buf_mem_new(int init_size) {
    struct buf_mem *buf = (struct buf_mem *)malloc(sizeof(struct buf_mem));
    if (buf == NULL) return NULL;

    buf->data = (char *)malloc(init_size);
    if (buf->data == NULL) {
        free(buf);
        return NULL;
    }

    buf->length = 0;
    buf->max = init_size;
    return buf;
}

// TODO: review symbollic base, end constraints cases featuring for example formal int init_size

/*
 * CASE buf == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * (buf==null) & (Base(buf)==0) & (End(buf)==0) & (%ret==null) & (Base(%ret)==0) & (End(%ret)==0)
 *
 * CASE buf != NULL && buf->data == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * Freed(buf) & (y1==null) & (Base(y1)==0) & (End(y1)==0) & (%ret==null) & (Base(%ret)==0) & (End(%ret)==0)
 *
 * CASE buf != NULL && buf->data != NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * (buf+0) -(8)-> (y1) * (buf+8) -(8)-> (y2) * (buf+16) -(8)-> (y3) * (y2+0) -(init_size)-> block
 * (Base(buf)==buf+0) & (End(buf)==buf+24) & (Base(y2)==y2+0) & (End(y2)==y2+init_size) & (y1==0) & (y3==init_size) & (%ret==buf)
 *
 * Expected error contracts:
 * <empty>
 */
