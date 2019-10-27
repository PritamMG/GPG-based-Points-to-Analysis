#include<stdio.h>
#include<stdlib.h>

int *x, *y, *z, *u, *s, **p, a, b, c, d, e;

//static __attribute__ ((noinline)) void foo()
void foo()
{
	int r;
	x = &a;  
	if (r)
	{
		y = &b;				
		u = &d;
	}
	else
	{
		z = &c; 
		s = &e;
 	}
	*p = y;   
}

int main()
{
	int r;
	y = &a;
	p = &z;
	if (r)
		foo();
}


