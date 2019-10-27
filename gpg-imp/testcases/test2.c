#include<stdio.h>
#include<stdlib.h>

struct tp{
	int data;
	int *f, *h;
	unsigned char *g;
	float *m;
	struct tp *next;
};


static void reverse(struct tp** head_ref)
{
    struct tp* prev   = NULL;
    struct tp* current = *head_ref;
    struct tp* next;
    while (current != NULL)
    {
        next  = current->next;  
        current->next = prev;   
        prev = current;
        current = next;
    }
    *head_ref = prev;
}

	struct tp *t1, *t2, *t3, t4, t5;
	int a, b, d;	
	unsigned char c;
	float e;
	int **x, *y, *z;

void foo()
{
	t1->f = &a;

	t2->h = &b;

	t3->m = &e;

	y = &a;

	*x = &b;

	y  = &d;

	z = &b;
}

int main()
{
	foo();

	#if 0
	t2.next = &t3;
	t2.data = 5;
	t3.next = &t4;
	t3.data = 6;
	t4.next = &t5;
	t4.data = 7;
	t5.next = NULL;
	t5.data = 8;

	t1 = &t2;

	reverse(&t1);
	#endif

	#if 0
	t2.f = &a;

	t1 = &t2;

	t1->f = &b;
	t2.g = &a;
	t1->g = &c;
	t1->h = &d;
	#endif

	return 0;
}
