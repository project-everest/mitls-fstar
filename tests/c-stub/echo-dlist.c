/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "echo-memory.h"
#include "echo-dlist.h"

/* -------------------------------------------------------------------- */
static const void *const _sentinel = (void*) &_sentinel;

#define DLIST_SENTINEL _sentinel

/* -------------------------------------------------------------------- */
dlist_t* dlist_new (void) {
    dlist_t *the = NEW(dlist_t, 1);

    the->data = (void*) DLIST_SENTINEL;
    the->next = the;
    the->prev = the;

    return the;
}

/* -------------------------------------------------------------------- */
void dlist_free(dlist_t *the, void (*freecb)(void *)) {
    dlist_t *current = NULL;

    assert(the->data == DLIST_SENTINEL);

    current = the->next;
    while (current != the) {
        dlist_t *next = the->next;

        if (current->data != NULL && freecb != NULL)
            freecb(current->data);
        free(current);
        current = next;
    }
    free(the);
}

/* -------------------------------------------------------------------- */
int dlist_empty(const dlist_t *the) {
    assert(the->data == DLIST_SENTINEL);
    return the->next == the;
}

/* -------------------------------------------------------------------- */
void dlist_push(dlist_t *the, void *data) {
    dlist_t *node = NULL;

    assert(the->data == DLIST_SENTINEL);

    node = NEW(dlist_t, 1);
    node->data = data;
    node->prev = the->prev;
    node->next = the;

    the->prev->next = node;
    the->prev = node;
}

/* -------------------------------------------------------------------- */
int dlist_pop(dlist_t *the, void **data) {
    dlist_t *node = NULL;

    assert(the->data == DLIST_SENTINEL);

    if (*data != NULL)
        *data = NULL;

    if (the->next == the)
        return 0;

    node = the->next;
    node->next->prev = node->prev;
    node->prev->next = node->next;

    if (*data != NULL)
        *data = node->data;
    free(node);

    return 1;
}
