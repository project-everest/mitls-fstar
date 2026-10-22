#ifndef CUSTARD_OPTION_H
#define CUSTARD_OPTION_H

/*
 * The layout Custard's direct-to-C backend gives a specialization of
 * FStar.Pervasives.Native.option: a tag enum (None = 0, Some = 1, in
 * constructor order) followed by a union holding the Some payload.
 *
 * The generated header names each specialization after its payload (e.g.
 * FStar_Pervasives_Native_option__channel).  The stubs are compiled on their
 * own, without that header, so they declare the same layout under a local
 * name; only the layout crosses the boundary.
 */
#define CUSTARD_NONE 0
#define CUSTARD_SOME 1

#define CUSTARD_OPTION_TYPE(name, T)                                       \
  typedef struct name##_s {                                                \
    enum name##_tags { name##_none = CUSTARD_NONE, name##_some = CUSTARD_SOME } tag; \
    union {                                                                \
      T Some;                                                              \
    } val;                                                                 \
  } name

#endif /* CUSTARD_OPTION_H */
