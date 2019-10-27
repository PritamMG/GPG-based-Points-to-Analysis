#include<stdio.h>
#include<stdlib.h>

int **x, **y, *z, *w;
int a, b, c, d;

struct tp
{
	void (*fp)();
};

struct tp *t;

void (*fp1)();
void (*fp2)();

void f1()
{
	z = &a;
}

void f2()
{
	z = &b;
}

void f3()
{
	fp1();
}

void f4()
{
	f3();
}

void f5()
{

	t = (struct tp*)malloc(sizeof(struct tp));

	if(a)
		t->fp = f1;
	else
		t->fp = f2;

	f4();
}

void f6()
{
	fp1 = f2;

	f4();
}

void f7()
{
	if(a)
		fp1 = f1;
	else
		fp1 = f2;

	f4();
}

void f8()
{
	if(a)
		fp1 = f1;

	f4();
}

void f9()
{
	fp1();

	if(a)
		fp1();
	else
		fp1();
		
	z = &a;

	fp1();
}

int main()
{
//	f9();

//	fp1 = f1;

	f5();

	fp1 = t->fp;

	fp1();

	#if 0
	f5();

	f6();

	f7();

	f8();
	#endif	
}
