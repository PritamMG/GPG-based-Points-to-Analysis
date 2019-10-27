/*
 * Profile.h
 *
 *  Created on: 24-Jun-2016
 *      Author: prasanna
 */

#ifndef _PROFILE_H_
#define _PROFILE_H_

//#define PROFILE
#ifdef PROFILE

#define MAX_FUN 9999
#define CALL_DEPTH 1999

void timer_start(unsigned int funId);
void timer_end(unsigned int funId);
unsigned int next_prof_id(void);
void init_profile_stats(void);
void print_profile_stats(void);
unsigned long long get_curr_time();

extern char* id2name[MAX_FUN];
#define PRINT_PROFILE_STATS() print_profile_stats()
#define INIT_PROFILE_STATS() init_profile_stats()

#define FUNBEGIN()                                          \
    static unsigned int _fun_prof_id = 0;                        \
    /*fprintf(stderr, "<== %s\n", __func__);*/                       \
    if (!_fun_prof_id)                                           \
    {                                                            \
        _fun_prof_id = next_prof_id();                           \
        id2name[_fun_prof_id] = (char*)__func__;                        \
    } else { /* nothing */ }                                     \
    timer_start(_fun_prof_id)                                    \


#define FUNEND() timer_end(_fun_prof_id)

/* careful: we want to use
 *     if (..) RETURN(x, y); else something
 * so we use this funny looking form.
 * otherwise "semicolon" at the end of RETURN will be treated as a
 * separate stmt
 */
#define RETURN(_retval)                          \
    if (1) { FUNEND(); /*fprintf(stderr, "==> %s\n", __func__);*/ return (_retval); } else /*nothing*/
#define RETURN_VOID()                                          \
    if (1) { FUNEND(); /*fprintf(stderr, "==> %s\n", __func__);*/ return; } else /*nothing*/

#define BEGIN_PROFILE()                                          \
		unsigned long long loop_time = get_curr_time();          \


#define END_PROFILE(id) \
  fprintf(stderr, "Time taken for  %s is %15llu\n", id, (get_curr_time() - loop_time)); \



#else /* no profiling */

#define FUNBEGIN() (void)0
#define FUNEND() (void)0
#define RETURN(_retval) return (_retval)
#define RETURN_VOID() return
#define PRINT_PROFILE_STATS() (void)0
#define INIT_PROFILE_STATS() (void)0
#define BEGIN_PROFILE() (void)0
#define END_PROFILE(id) (void)0

#endif
#endif /* _PROFILE_H_ */
