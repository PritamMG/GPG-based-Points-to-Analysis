#include<stdio.h>

int a, b, *p, *q, *s, **x;

void foo()
{
	p = &a;

	*x = &b;

	q = p;
}

int main()
{
	x = &p;

	foo();
}

