#include<stdio.h>

int **x, *y, *z;
int a, b, c, d, e;

void foo()
{
	z = &e;

	while(a)
	{
		if(b)
			x = &z;
		else
			y = &d;
	}
}

int main()
{
	foo();
}

