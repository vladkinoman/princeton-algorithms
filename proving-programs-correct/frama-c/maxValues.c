#include <stdio.h>
#include <string.h>
#include <limits.h>

/*@ requires N >= 0 && \valid_read(a + (0..N-1));
	
	assigns \nothing;
	
	behavior empty: 
		assumes N == 0; 
		ensures \result == 0;
	
	behavior not_empty: 
		assumes 0 < N;
	
	ensures 0 <= \result < N; 
	ensures 
		\forall integer i; 
		0 <= i < N ==> a[i] <= a[\result]; 
	ensures 
		\forall integer i; 
		0 <= i < \result ==> a[i] < a[\result];
	
	complete behaviors; 
	disjoint behaviors;
*/ 

int max(int* a, int N)
{
    if (N == 0) 
    { 
    	return 0; 
    }
    int i;
	int max = 0;
	/*@ 
		loop invariant 0 <= i <= N; 
		loop invariant 0 <= max < N; 
		loop invariant 
			\forall integer k; 
			0 <= k < i ==> a[k] <= a[max]; 
		loop invariant 
			\forall integer k; 
			0 <= k < max ==> a[k] < a[max]; 
		loop assigns max, i; 
		loop variant N-i; 
	*/ 
	for (i = 0; i < N; i++) 
	{ 
		if (a[max] < a[i]) 
		{ 
			max = i; 
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
	printf("max_from_arr = %i\n", a[max_index]);
	return 0;
}