#include<stdio.h>
#include<stdlib.h>

int **x, a, b;

void foo()
{
	x = (int **)malloc(10*sizeof(int));
}

void bar()
{
	int i = 0;

	for(; i < 10; i++)
	{
		x[i] = &a;
	}
}

int main()
{
	foo();
	bar();

	return 0;
}
