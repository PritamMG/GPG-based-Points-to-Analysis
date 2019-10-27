#include<stdio.h>


struct node{
	int *m , *n;
};

struct node n1, n2, n3, n4, n5;
struct node *t1, *t2, *t3, *t4, *t5;
int a, b, c, d, e;
int *p, *q, *r, *s;
int **x, **y, **z;

void g()
{
	t1->m = &a;
	t2->m = p;
	t2->n = &b;
	t3->m = q;
	t3->n = &c;
	t4->m = t3->m;
}

void f()
{
	t1 = &n1;

	g();
}

void h()
{
	t2 = &n2;
	t3 = &n3;
	t4 = &n4;

	g();
}

int main()
{
	p = &d;
	q = &e;

	t1 = &n5;
	t2 = &n5;
	t3 = t2;
	t4 = &n3;
	n5.m = &d;
	n3.m = p;

	h();

	f();
}

