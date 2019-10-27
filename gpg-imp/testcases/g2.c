#include<stdio.h>
#include<stdlib.h>

int *x, *y, *z, *u, *s, **p, a, b, c, d, e;

static __attribute__ ((noinline)) void foo()
//void foo()
{
	int r;
	x = &a;  
	if (r)
		y = &b;
	else
		z = &c; 
	*p = y;   
}

int main()
{
	int r;
	x = &b;
	y = &a;
	p = &z;
	if (r)
		foo();
}


/***************************************************************************************

- Problem in compiling

	- If we retain the function header 
		static __attribute__ ((noinline)) void foo()
	  and comment out 
		void foo()
          then we get the following error:
	
		lto1: internal compiler error: Segmentation fault

          The error goes away if we comment out the statement

                l_temp.insert(lnode);

          in function void collectUpwardExposedVersions(GPUSet gen, struct cgraph_node *cnode)
	  in file GPG.cc. The statement can be found by searching for CHECK or SEGMENTATION 
          or FAULT.

	  The error goes away if we change the funtion header in this file to
          plain "void foo()".

- Function foo gets inlined. For us to introduce dependences, we need indirections of 
  upwards exposed variables. With linlined code, all indirections get redued and 
  everything is 1/0 and a single GPB. I am puzzled how it happens without coalescingDFA 
  though. Have you optimized the code to do the coalescing DFA only when there are
  indirections of upwards exposed variables? If yes, it's a clever (and very useful) 
  optimization, except that we are unable test coalescing exhaustively.

****************************************************************************************/
