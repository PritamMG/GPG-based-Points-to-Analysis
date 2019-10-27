#include<stdio.h>

int *a, *b, *c, *d, *e;
int **p, **q;
int t1, *t2;
int m ,n , o;

void foo()
{
	c = &o;

	if(m)
	{
		a = &m;
	}
	else
	{
		b = &n;
	}
	
	*p = &t1;
}

int main()
{
	p = &t2;

	foo();
} 
