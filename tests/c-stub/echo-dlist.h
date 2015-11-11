/* -------------------------------------------------------------------- */
#ifndef ECHO_DLIST_H__
# define ECHO_DLIST_H__

/* -------------------------------------------------------------------- */
typedef struct dnode {
    void *data;
    struct dnode *next;
    struct dnode *prev;
} dnode_t;

typedef struct dnode dlist_t;

/* -------------------------------------------------------------------- */
dlist_t* dlist_new (void);
void     dlist_free(dlist_t *the, void (*free)(void *));

int  dlist_empty(const dlist_t *the);
void dlist_push (dlist_t *the, void *data);
int  dlist_pop  (dlist_t *the, void **data);

#endif /* !ECHO_DLIST_H__ */
