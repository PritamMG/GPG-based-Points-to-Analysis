#include<stdio.h>

int **x, *y, *z;

void foo()
{
	int a;
	
	z = NULL;

	if(a)
		*x = z;
	else
		*x = y;
}

int main()
{
	foo();
}
