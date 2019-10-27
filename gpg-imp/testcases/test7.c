#include<stdio.h>

int ***x, **y, *z;

void foo()
{
	**x = z;

	*x = y;
}

int main()
{
	foo();
}
