/*
 * Profile.cpp
 *
 *  Created on: 24-Jun-2016
 *      Author: prasanna
 */


#include "Profile.h"
#ifdef PROFILE
#include <stdlib.h>
#include<stdio.h>
#include <sys/time.h>
#include <assert.h>

/* stores the time when we start executing instructions in
 * the current function.  This could happen at function
 * entry, or when we return from a callee.
 */
static unsigned long long start_time[MAX_FUN];
static unsigned long long cstart[MAX_FUN];

/* stores total time spent in the function, cumulative and
 * self */
static unsigned long long cum_time[MAX_FUN];
static unsigned long long self_time[MAX_FUN];

/* number of calls to this function */
static unsigned long num_calls[MAX_FUN];

/* keeps track of the call stack. Required so that we
 * increment time in the caller once we return from callee.
 */
static unsigned int call_stack[CALL_DEPTH];

/* Top of the call stack */
static unsigned int cTop = 0;

/* Current function we are looking into */
static unsigned int funcId;


/* helper function to return current timeval as
 * unsigned long long */
static unsigned long long time_now()
{
    struct timeval t;
    gettimeofday(&t, NULL);
    return 1000000LL * t.tv_sec + t.tv_usec;
}

unsigned long long get_curr_time()
{
	return time_now();
}


void timer_start(unsigned int funId)
{
    unsigned long long now_time = time_now();
    /* Compute the time spent in caller and store it */
    unsigned int caller = call_stack[cTop];
    if (caller)
        self_time[caller] += now_time - start_time[caller];

    /* push current function, and start its timer */
    ++cTop;
    assert(cTop < CALL_DEPTH);
    call_stack[cTop] = funId;
    cstart[funId] = start_time[funId] = now_time;
    ++num_calls[funId];

    return;
}

void timer_end(unsigned int funId)
{
    unsigned long long now_time = time_now();
    /* some sanity check */
    assert(call_stack[cTop] == funId);
    assert(cTop > 0);
    /* stop timer for current function, and pop it from call stack */
    self_time[funId] += now_time - start_time[funId];
    cum_time[funId]  += now_time - cstart[funId];

    --cTop;

    /* start the clock for the caller */
    unsigned int caller = call_stack[cTop];
    if (caller)
        start_time[caller] = now_time;

    return;
}

/* id generator for functions */
static int curr_fun_id = 0;
unsigned int next_prof_id(void)
{
    ++curr_fun_id;
    assert(curr_fun_id < MAX_FUN);
    return curr_fun_id;
}

char* id2name[MAX_FUN];
void print_profile_stats(void)
{
    int i;
    cum_time[0] = self_time[0] = time_now() - start_time[0];

    fprintf(stderr,"\n");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"\n");
    fprintf(stderr,"  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfTIME", "%", "CumTIME", "%");
    fprintf(stderr,"  %51s %15s %6s  %15s  %6s\n", "",                    " (uSec) ", "",  " (uSec)", "");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"\n");

    for (i = 1; i <= curr_fun_id; i++) {
        fprintf(stderr,"  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2name[i], num_calls[i],
               self_time[i], 100.0D*self_time[i]/self_time[0],
               cum_time[i],  100.0D*cum_time[i]/cum_time[0]);
    }
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"\n");
    fprintf(stderr,"  %51s %15llu  100.00  %15llu  100.00\n", id2name[0],
           self_time[0], cum_time[0]);
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"-------------------------------------------------------------");
    fprintf(stderr,"\n");

    FILE *fptr = fopen("stats.txt", "w");

    fprintf(fptr,"\n");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"\n");
    fprintf(fptr,"  %51s %15s %6s  %15s  %6s\n", "FUNCTION (  #Calls)", "SelfTIME", "%", "CumTIME", "%");
    fprintf(fptr,"  %51s %15s %6s  %15s  %6s\n", "",                    " (uSec) ", "",  " (uSec)", "");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"\n");

    for (i = 1; i <= curr_fun_id; i++) {
        fprintf(fptr,"  %40s (%8ld) %15llu  %6.2lf  %15llu  %6.2lf\n",
               id2name[i], num_calls[i],
               self_time[i], 100.0D*self_time[i]/self_time[0],
               cum_time[i],  100.0D*cum_time[i]/cum_time[0]);
    }
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"\n");
    fprintf(fptr,"  %51s %15llu  100.00  %15llu  100.00\n", id2name[0],
           self_time[0], cum_time[0]);
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"-------------------------------------------------------------");
    fprintf(fptr,"\n"); 
    fclose(fptr);
}

void init_profile_stats(void)
{
    /* Compute the time spent in caller and store it */
    cum_time[0] = start_time[0] = time_now();
    id2name[0] = (char*)"TOTAL TIME";
}

#endif


