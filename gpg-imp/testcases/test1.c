#include<stdio.h>

#if 0
int **x;
int *y,*z,**p, *w;
int a,b,c, d;

int * foo(int **m)
{
	int *r;

	y = &a;

	if(c)
	{
		x = &y;
	}

	*x = &b;

	r = &d;

	return r;
}

int main()
{
	x = &z;
	z = &c;

	z = foo(x);
}
#endif

int *a, *b, *c, *d, *e;
int **p, **q;
int m ,n , o;

void g()
{
	while(o)
	{
		a =&m;
		*q = a;

//		if(n)
		{
			q = &b;
		}
	}
	
	e = *p;
	q = &e;	
}

void f()
{
	p = &c;
	q = &d;
	d = &n;
	
	g();

	*q = &o;
}

int main()
{
	f();
} 
