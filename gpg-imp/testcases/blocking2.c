#include<stdio.h>

int a, b, *p, *q, *s, **x;

void foo()
{
	x = &s;

	p = &b;

	q = *x;
}

int main()
{
	x = &p;

	foo();
}

