#include<stdio.h>

int m, n, o, l, s;
int *a, *b, *c, *d, *e;
int **p, **q, **r;

void g()
{
	while(l)
	{
		r = &a;
		*q = &m;

		if(s)
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
