#include <stdio.h>
#include <string.h>
#include <limits.h>

/*@ requires N >= 1 && \valid_read(a + (0..N-1));

	ensures INT_MIN <= \result <= INT_MAX; 
	ensures 
		\forall integer k; 
			0 <= k < N ==> a[k] <= \result; 
	ensures 
		\exists integer j; 
			0 <= j < N && \result == a[j];
*/ 
int max(int* a, int N)
{
    int i;
	int max = a[0];
	/*@ 
		loop invariant 1 <= i <= N;
		loop invariant 
			\forall integer k; 
			0 <= k < i ==> a[k] <= max; 
		loop invariant 
			\exists integer j; 
			0 <= j < i && max == a[j];
		loop assigns max, i; 
		loop variant N-i; 
	*/ 
	for (i = 1; i < N; i++) 
	{ 
		if (max < a[i]) 
		{ 
			max = a[i]; 
		} 
	}

	return max;
}

int main()
{
    int N = 6;
    //int* a;
    //a = (int*) malloc(N*sizeof(int));
    int a[N];
    memcpy(a, (int[]) {23, 50, 61, 124, 562, 1000}, sizeof a);
    //a = {23, 50, 61, 124, 562, 1000};
    //*(a + 0) = 23;
    //*(a + 1) = 50;
    //*(a + 2) = 61;
    //a[3] = 124;
    //a[4] = 563;
    //a[5] = 1000;
    // max from odd numbers
    int max_index = max(a, N);
	printf("max_from_arr = %i\n", max_index);
	return 0;
}
