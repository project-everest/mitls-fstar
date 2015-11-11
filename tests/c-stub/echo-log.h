/* -------------------------------------------------------------------- */
#ifndef ECHO_LOG_H__
# define ECHO_LOG_H__

/* -------------------------------------------------------------------- */
#include <log4c.h>

/* -------------------------------------------------------------------- */
extern log4c_category_t *logcat;

/* -------------------------------------------------------------------- */
#define LOGPRIO (log4c_category_get_priority(logcat))

#define LOG_FATAL  LOG4C_PRIORITY_FATAL
#define LOG_ALERT  LOG4C_PRIORITY_ALERT
#define LOG_CRIT   LOG4C_PRIORITY_CRIT
#define LOG_ERROR  LOG4C_PRIORITY_ERROR
#define LOG_WARN   LOG4C_PRIORITY_WARN
#define LOG_NOTICE LOG4C_PRIORITY_NOTICE
#define LOG_INFO   LOG4C_PRIORITY_INFO
#define LOG_DEBUG  LOG4C_PRIORITY_DEBUG

/* -------------------------------------------------------------------- */
void initialize_log4c(void);

void elog(int level, const char *format, ...)
    __attribute__((format(printf, 2, 3)));

void _evlog(int severity, const char *msg);

#endif /* !ECHO_LOG_H__ */
