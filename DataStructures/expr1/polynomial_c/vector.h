#ifndef __VECTOR__
#define __VECTOR__

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <memory.h>
#include "common.h"

//////// Type Definitions ////////

typedef struct Vector_ {
    size_t size;
    size_t capacity;
    void **data;
    fn_ptr *deleter;
} Vector;

//////// Implementation of Vector ////////

Vector *new_vector(void) {
    Vector *vec = (Vector *) malloc_throw(sizeof(Vector));
    vec->size = 0;
    vec->capacity = 0;
    vec->data = malloc_throw(0);
    vec->deleter = malloc_throw(0);
    return vec;
}

void delete_vector(Vector **vec) {
    void **data = (*vec)->data;
    fn_ptr *deleter = (*vec)->deleter;
    for (size_t i = 0; i != (*vec)->size; ++i) {
        if (data[i] != NULL) {
            deleter[i](data[i]);
        }
    }
    safe_free((void **) &data);
    safe_free((void **) &deleter);
    safe_free((void **) vec);
}

void *vector_back(const Vector *vec) {
    assert(vec->size > 0);
    return vec->data[vec->size - 1];
}

void vector_pop_back(Vector *vec) {
    assert(vec->size > 0);
    --vec->size;
    vec->deleter[vec->size](vec->data[vec->size]);
}

void vector_reserve_throw(Vector *vec, size_t capacity) {
    if (vec->capacity >= capacity) {
        return;
    }
    if (vec->capacity == 0) {
        vec->capacity = 1;
    }
    while (vec->capacity < capacity) {
        vec->capacity <<= 1;
    }
    vec->data = realloc(vec->data, vec->capacity * sizeof(void *));
    vec->deleter = realloc(vec->deleter, vec->capacity * sizeof(void *));
    assert(vec->data != NULL && vec->deleter != NULL);
}

void vector_append(Vector *vec, void *new_value) {
    vector_reserve_throw(vec, vec->size + 1);
    vec->data[vec->size] = new_value;
    vec->deleter[vec->size] = free;
    ++vec->size;
}

void vector_copy_append(Vector *vec, const void *new_value,
                        fn_copier copy) {
    vector_reserve_throw(vec, vec->size + 1);
    void *new_ptr = malloc_throw(sizeof(void *));
    copy(new_ptr, new_value);
    vec->data[vec->size] = new_ptr;
    vec->deleter[vec->size] = free;
    ++vec->size;
}

void vector_append_with_deleter(Vector *vec, void *new_value,
                                fn_ptr deleter) {
    vector_reserve_throw(vec, vec->size + 1);
    vec->data[vec->size] = new_value;
    vec->deleter[vec->size] = deleter;
    ++vec->size;
}

void vector_copy_append_with_deleter(Vector *vec, const void *new_value,
                                     fn_copier copy, fn_ptr deleter) {
    vector_reserve_throw(vec, vec->size + 1);
    void *new_ptr = malloc_throw(sizeof(void *));
    copy(new_ptr, new_value);
    vec->data[vec->size] = new_ptr;
    vec->deleter[vec->size] = deleter;
    ++vec->size;
}

void vector_insert(Vector *vec, size_t index, void *new_value) {
    assert(index <= vec->size);
    vector_reserve_throw(vec, ++vec->size);
    for (size_t i = vec->size - 1; i != index; --i) {
        vec->data[i] = vec->data[i - 1];
        vec->deleter[i] = vec->deleter[i - 1];
    }
    vec->data[index] = new_value;
    vec->deleter[index] = free;
}

void vector_insert_with_deleter(Vector *vec, size_t index,
                                void *new_value, fn_ptr deleter) {
    assert(index <= vec->size);
    vector_reserve_throw(vec, ++vec->size);
    for (size_t i = vec->size - 1; i != index; --i) {
        vec->data[i] = vec->data[i - 1];
        vec->deleter[i] = vec->deleter[i - 1];
    }
    vec->data[index] = new_value;
    vec->deleter[index] = deleter;
}

void vector_copy_concat(Vector *dst, const Vector *vec, fn_copier copy) {
    size_t new_size = dst->size + vec->size;
    vector_reserve_throw(dst, new_size);
    for (size_t i = 0; i != vec->size; ++i) {
        void *new_ptr = malloc_throw(sizeof(void *));
        copy(new_ptr, vec->data[i]);
        dst->data[dst->size + i] = new_ptr;
        dst->deleter[dst->size + i] = vec->deleter[i];
    }
    dst->size = new_size;
}

#endif  // __VECTOR__
