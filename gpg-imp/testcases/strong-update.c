#include<stdio.h>

int **x, *a, b, c, *d;

void foo()
{
	a = &b;

//	if(b)
	x = &a;

	*x = &c;
}

int main()
{
	x = &d;

	foo();
}
