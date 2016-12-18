#include <stdio.h>

/*@ 
    requires \valid(x) && \valid(y);
    
    ensures (*x == \old(*y)) && (*y == \old(*x));
*/
void swap(int* x, int *y)
{  
    int tmp;
    tmp = *x;
    *x = *y;
    *y = tmp;
}

int main() 
{
	int a, b;
	a = 20;
	b = 40;
	swap(&a, &b);
	printf("a = %d\nb = %d", a, b);
	return 0;
}
