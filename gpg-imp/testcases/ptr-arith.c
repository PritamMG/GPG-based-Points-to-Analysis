#include<stdio.h>
#include<stdlib.h>

int a, b, c;
int *x[10];
int **y;

void foo()
{
	int i;

	for(i=0; i < 10; i++)
	{
		x[i] = &a;
	}

	y = (int **)malloc(10*sizeof(int));

	for(i=0; i < 10; i++)
	{
		y[i] = x[i];
	}
}

int main()
{
	foo();

	return 0;
}
