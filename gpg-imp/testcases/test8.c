#include<stdio.h>

int **x, *y, *z, a, b;

void foo()
{
	x = &y;
//	y = &b;

	z = *x;

}

int main()
{

	y = &a;

	foo();
}
