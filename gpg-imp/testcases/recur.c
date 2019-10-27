#include<stdio.h>
#include<stdlib.h>

int **x, **y, *z, *w;
int a, b, c, d;

void foo()
{
	z = &b;

	#if 1
	if(a)
	{
		z = &a;
	
		foo();
	}
	#endif
}

void error(char *x, int y)
{
	exit(1);
}

void no_mem_exit(char *where)
{
//   snprintf(errortext, ET_SIZE, "Could not allocate memory: %s",where);
   error (where, 100);
}

char *items[10];

void bar(char *buf)
{
	char *p;

	p = buf;

	*p = 0;
	
	items[3] = p;
	
	if(a)
		exit(1);
}

int main()
{
	#if 0
	char *s;

	no_mem_exit(s);

	bar(s);
	#endif

	foo();
}
