#ifndef __LINKED_LIST__
#define __LINKED_LIST__

#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include "common.h"

//////// Type Definitions ////////

typedef struct LLNode_ {
    void *value;
    struct LLNode_ *next;
} LLNode, LinkedList;

//////// Implementation of Linked List ////////

LLNode **new_linked_list(void) {
    LLNode **head = (LLNode **) malloc_throw(sizeof(LLNode *));
    *head = NULL;
    return head;
}

void delete_linked_list(LLNode **head) {
    LLNode *curr = *head;
    LLNode *prev = NULL;
    while (curr != NULL) {
        prev = curr;
        curr = curr->next;
        safe_free((void **) &prev);
    }
}

void append(LLNode **head, void *new_value) {
    LLNode **curr = head;
    while (*curr != NULL) {
        curr = &(*curr)->next;
    }
    LLNode *new_LLNode = (LLNode *) malloc_throw(sizeof(LLNode));
    new_LLNode->value = new_value;
    new_LLNode->next = NULL;
    *curr = new_LLNode;
}

void insert(LLNode **head, size_t index, void *new_value) {
    LLNode **curr = head;
    size_t count = 0;
    while (count != index && *curr != NULL) {
        curr = &(*curr)->next;
        ++count;
    }
    assert(count == index);
    LLNode *new_LLNode = (LLNode *) malloc_throw(sizeof(LLNode));
    new_LLNode->value = new_value;
    new_LLNode->next = *curr;
    *curr = new_LLNode;
}

size_t find_if(LLNode **head, int (*eligible)(void *)) {
    size_t index = 0;
    for (LLNode *curr = *head; curr != NULL; curr = curr->next) {
        if (eligible(curr->value)) {
            return index;
        }
        ++index;
    }
    return -1;
}

void reverse(LLNode **head) {
    /* Reverse a linked list in-place. */
    LLNode *helper[3];  // Stores a circular queue.
    if ((helper[0] = *head) == NULL || (helper[1] = (*head)->next) == NULL) {
        return;
    }
    helper[2] = helper[1]->next;
    helper[0]->next = NULL;
    size_t offset = 0;
    for (; helper[(offset + 2) % 3] != NULL; ++offset) {
        helper[(offset + 1) % 3]->next = helper[offset % 3];
        helper[offset % 3] = helper[(offset + 2) % 3]->next;
    }
    helper[(offset + 1) % 3]->next = helper[offset % 3];
    *head = helper[(offset + 1) % 3];
}

void remove_if(LLNode **head, int (*going_to_remove)(void *)) {
    LLNode **curr = head;
    LLNode *entry = NULL;
    while ((entry = *curr) != NULL) {
        if (going_to_remove(entry->value)) {
            *curr = entry->next;
            safe_free((void **) &entry);
        } else {
            curr = &entry->next;
        }
    }
}

void sort_linked_list(LLNode **head, int (*less_than)(void *, void *)) {
    /* Bubble sort. */
    if (*head == NULL || (*head)->next == NULL) {
        return;
    }
    LLNode **curr = NULL, *next = NULL;
    size_t size = 1;
    for (curr = head; (*curr)->next != NULL; curr = &(*curr)->next) {
        ++size;
    }
    for (size_t i = size - 1; i != 0; --i) {
        curr = head;
        for (size_t j = 0; j != i; ++j) {
            if (less_than((*curr)->next->value, (*curr)->value)) {
                next = (*curr)->next;
                (*curr)->next = next->next;
                next->next = *curr;
                *curr = next;
            }
            curr = &(*curr)->next;
        }
    }
}

#endif  // __LINKED_LIST__
