#include <stdio.h>
#include <string.h>


/*@
    axiomatic CountAxiomatic
    {
        logic int Count{L} (int a[], integer N)
            reads a[0..N-1];
        
        axiom CountEmpty:
            \forall int a[], integer N;
                N <= 0 ==> Count(a, N) == 0;

        axiom CountOneHit:
            \forall int a[], integer N;
                N % 2 == 0 && a[N] % 2 != 0 ==> Count(a, N + 1) == Count(a, N) + 1;
        
        axiom CountOneMiss:
            \forall int a[], integer N;
                !(N % 2 == 0 && a[N] % 2 != 0) ==> Count(a, N + 1) == Count(a, N);
    }
*/

/*@ requires N >= 0 && \valid_read(a + (0..N-1));
    
    assigns \nothing;
    
    ensures \result == Count(a, N);
    ensures 0 <= \result < N;
*/
int count(int a[], int N)
{
	int i, x;
	/*@ loop invariant 0 <= i <= N;
	    loop invariant 0 <= x <= i;
	    loop invariant x == Count(a, i);
	    loop assigns i, x;
	    loop variant N - i;
	*/
	for (i = 0, x = 0; i < N; i++)
	{
		if (i % 2 == 0 && a[i] % 2 != 0)
		{
			x = x + 1;
		}
	}

	return x;
}

int main()
{
    	// count of odd entries that are at the even positions
    	int N = 6;
    	int a[N];
    	memcpy(a, (int[]) {23, 50, 61, 124, 562, 1000}, sizeof a);
	int result = count(a, N);
	printf("result = %i\n", result);
	
	return 0;
}
