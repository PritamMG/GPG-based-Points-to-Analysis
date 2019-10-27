#include<stdio.h>

int main()
{
	unsigned int res = 1;
	int i;

	for(i=0; i < 63; i++)
	{
		printf("\ni= %d, res = %u\n", i, res);
		res *= 2;
	}

	printf("\nres = %u\n", res);
}
