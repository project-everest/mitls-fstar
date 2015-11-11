/* -------------------------------------------------------------------- */
#include <sys/types.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include "echo-memory.h"

/* -------------------------------------------------------------------- */
void* xmalloc(size_t size) {
    void *p = malloc(size);

    if (p == NULL) {
        if (size == 0)
            return xmalloc(1u);
        abort();
    }
    return p;
}

/* -------------------------------------------------------------------- */
void* xrealloc(void *p, size_t size) {
    void *newp = realloc(p, size);

    if (newp == NULL) {
        if (size == 0)
            return NULL;
        abort();
    }
    return newp;
}

/* -------------------------------------------------------------------- */
void* xcalloc(size_t nmemb, size_t size) {
    void *p = calloc(nmemb, size);

    if (p == NULL)
        abort();
    return p;
}

/* -------------------------------------------------------------------- */
#ifdef WIN32
char *strndup(const char *s, size_t sz) {
    size_t  slen = strlen(s);
    char   *new  = NULL;

    slen = (slen > sz) ? sz : slen;
    new  = malloc (slen + 1);

    if (new == NULL)
        return NULL;

    memcpy(new, s, slen);
    new[slen] = '\0';

    return new;
}
#endif

char* xstrdup(const char *s) {
    if ((s = strdup(s)) == NULL)
        abort();
    return (char*) s;
}

char* xstrndup(const char *s, size_t n) {
    if ((s = strndup(s, n)) == NULL)
        abort();
    return (char*) s;
}

/* -------------------------------------------------------------------- */
char* xjoin(const char *s, ...) {
    /*-*/ size_t   len  = 0;
    const char    *p    = NULL;
    /*-*/ size_t   outi = 0u;
    /*-*/ char    *out  = NULL;
    /*-*/ va_list  ap;

    va_start(ap, s);
    for (p = s; p != NULL; p = va_arg(ap, char*))
        len += strlen(p);
    va_end(ap);

    out = NEW(char, len + 1);

    va_start(ap, s);
    for (outi = 0u, p = s; p != NULL; p = va_arg(ap, char*)) {
        const size_t plen = strlen(p);
        memcpy(&out[outi], p, plen);
        outi += plen;
    }
    va_end(ap);

    out[outi] = '\0'; return out;
}
