#include<stdio.h>

int *y, a, b, c;

void p();

void q()
{
	y = &b;

	p();
}

void p()
{
	if(c)
		y = &a;
	else
		q();
}

int main()
{
	p();
}
