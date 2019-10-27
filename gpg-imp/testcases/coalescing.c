#include<stdio.h>

int *x, *y, *z, **p, a, b, c;

void foo()
{
	*p = y;

	x = &a;
	y = &b;
	z = &c;
}

int main()
{
	foo();
}
