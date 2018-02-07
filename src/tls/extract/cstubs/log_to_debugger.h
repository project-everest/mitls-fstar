// log_to_debugger.h.  This works on Windows via mingw gcc.  it must begin
// force-included ahead of all miTLS source files.

extern void DbgPrint(const char *fmt, ...);

#define KRML_HOST_PRINTF DbgPrint
#define KRML_HOST_EPRINTF DbgPrint
