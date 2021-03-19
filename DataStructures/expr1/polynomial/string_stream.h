#ifndef __STRING_STREAM__
#define __STRING_STREAM__

#include <string.h>
#include "common.h"
#include "vector.h"

WRAP_UNWRAP(char)

SHALLOW_COPY(char)

typedef struct StringStream_ {
    Vector *data;
    size_t pos;
} StringStream;

StringStream *new_ss(void) {
    StringStream *ss = malloc_throw(sizeof(StringStream));
    ss->data = new_vector();
    ss->pos = 0;
    return ss;
}

StringStream *new_ss_from_c_string(const char string[]) {
    StringStream *ss = malloc_throw(sizeof(StringStream));
    ss->data = new_vector();
    ss->pos = 0;
    size_t length = strlen(string);
    vector_reserve_throw(ss->data, length);
    for (size_t i = 0; i != length; ++i) {
        vector_append(ss->data, wrap_char(string[i]));
    }
    return ss;
}

void delete_ss(StringStream **ss) {
    delete_vector(&(*ss)->data);
    safe_free((void **) ss);
}

void ss_feed(StringStream *ss, Vector *data) {
    vector_copy_concat(ss->data, data, char_copy);
}

void ss_feed_char(StringStream *ss, char chr) {
    vector_append(ss->data, wrap_char(chr));
}

int ss_eof(const StringStream *ss) {
    return ss->pos == ss->data->size;
}

int ss_good(const StringStream *ss) {
    return 0 <= ss->pos && ss->pos <= ss->data->size;
}

void ss_seek(StringStream *ss, size_t positions) {
    ss->pos += positions;
    assert(ss_good(ss));
}

size_t ss_tell(const StringStream *ss) {
    return ss->pos;
}

void ss_set_pos(StringStream *ss, size_t pos) {
    ss->pos = pos;
    assert(ss_good(ss));
}

void ss_rewind(StringStream *ss) {
    ss->pos = 0;
}

char ss_getchar(StringStream *ss) {
    if (ss_eof(ss)) {
        return EOF;
    }
    return unwrap_char(ss->data->data[ss->pos++]);
}

char ss_peek(const StringStream *ss) {
    if (ss_eof(ss)) {
        return EOF;
    }
    return unwrap_char(ss->data->data[ss->pos]);
}

#endif  // __STRING_STREAM__
