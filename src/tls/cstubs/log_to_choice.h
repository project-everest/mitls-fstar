// log_to_choice.h.  It must be force-included ahead of all miTLS source files.
// mitlsffi.c implements the remainder of the support.

#define LOG_TO_CHOICE 1

typedef void (*p_log)(const char *fmt, ...);
extern p_log g_LogPrint;

#define KRML_HOST_PRINTF (*g_LogPrint)
#define KRML_HOST_EPRINTF (*g_LogPrint)

