#ifndef __COMMON__
#define __COMMON__

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <memory.h>

#define WRAP_UNWRAP(type)                            \
void *wrap_##type(type value) {                      \
    type *ptr = (type *) malloc_throw(sizeof(type)); \
    *ptr = value;                                    \
    return ptr;                                      \
}                                                    \
type unwrap_##type(void *ptr) {                      \
    return *(type *) ptr;                            \
}

#define SHALLOW_COPY(type)                \
void type##_copy(void *dst, const void *from) { \
    memcpy(dst, from, sizeof(type));      \
}

//////// Type Definitions ////////

typedef void (*fn_ptr)(void *);

typedef void (*fn_copier)(void *, const void *);

//////// Helper functions ////////

void *malloc_throw(size_t size) {
    /* Make sure the allocation to be successful. */
    void *allocated = malloc(size);
    assert(allocated != NULL);
    return allocated;
}

void safe_free(void **p_ptr) {
    /* Avoid creating a dangling pointer. */
    assert(*p_ptr != NULL);
    free(*p_ptr);
    *p_ptr = NULL;
}

#endif  // __COMMON__
