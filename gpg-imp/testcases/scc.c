#include<stdio.h>

void g();
void h();

void f()
{
	printf("\nHi\n");

	g();
}

void g()
{
	printf("\nHi\n");

	f();

	h();
}

void h()
{
	printf("\nHi\n");

	g();
}

int main()
{
	f();

	h();
	
	return 0;
}

