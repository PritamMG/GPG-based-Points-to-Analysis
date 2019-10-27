#include<stdio.h>

int **x, **y, **z;
int *p, *q, *r;

float **m, **n, **o;
float *u, *v , *w;

char **f, **g, **h;
char *i, *j, *k;

int a, b, c;

void foo()
{
	x = &p;

	*y = q;

	r = &a;

	m = &u;
	
	n = &v;

	*f = i;

	g = &j;

	h = &k;

	o = &w;
}

int main()
{
	foo();

	return 0;
}

