
int ***x, **y, **z, **w;

void foo()
{
	int a;

	if(a)
		*x = y;
	else
		*x = z;
}

int *b, *c, d, *e;
	
int main()
{
	z = &e;
	x = &w;
	b = &d;
	w = &b;
	y = &c;

	foo();
}
