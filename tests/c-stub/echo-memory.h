/* -------------------------------------------------------------------- */
#ifndef ECHO_MEMORY_H__
# define ECHO_MEMORY_H__

/* -------------------------------------------------------------------- */
#include <sys/types.h>

/* -------------------------------------------------------------------- */
#define ARRAY_SIZE(A) (sizeof (A) / sizeof ((A)[0]))

/* -------------------------------------------------------------------- */
void* xmalloc(size_t size);
void* xrealloc(void *p, size_t size);
void* xcalloc(size_t nmemb, size_t size);

#define NEW(T, N) ((T*) xcalloc(N, sizeof(T)))

/* -------------------------------------------------------------------- */
char* xstrdup(const char *s);
char* xstrndup(const char *s, size_t n);
char* xjoin(const char *s, ...);

#endif /* !ECHO_MEMORY_H__ */
