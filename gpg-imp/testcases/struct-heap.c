#include<stdio.h>
#include<stdlib.h>

struct node{
	struct node *n;
	int d;
};

struct node *x;

void g()
{
	int a;

	while(a)
	{
		printf("%d\n", x->d);

		x = x->n;
	}
}

void f()
{
	struct node *y;
	int b;

	y = (struct node *)malloc(sizeof(struct node));

	x = y;

	while(b)
	{
		y->n = (struct node *)malloc(sizeof(struct node));

		y = y->n;
	}

	g();
}

int main()
{
	f();
}


