#include<stdio.h>

struct tp{
	int *a;
	float *b;
	char *c;
	int *d;
};

struct tp t1, t2;
struct tp *t3, *t4;

int x, y, z;
float m;
char n;

void foo()
{
	t3->a = &x;
	t3->d = &y;
	t3->c = &n;
	t3->b = &m;
}

int main()
{
	foo();

	return 0;
}
