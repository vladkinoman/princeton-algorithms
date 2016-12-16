#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*@
    axiomatic CountAxiomatic
    {
        logic int Count{L} (int* a, integer N)
            reads a[0..N-1];
        
        axiom CountEmpty:
            \forall int* a, integer N;
                N <= 0 ==> Count(a, N) == 0;

        axiom CountOneHit:
            \forall int* a, integer N;
               N % 2 == 0 && a[N] % 2 != 0 ==> Count(a, N + 1) == Count(a, N) + 1;
        
        axiom CountOneMiss:
            \forall int* a, integer N;
               !(N % 2 == 0 && a[N] % 2 != 0) ==> Count(a, N + 1) == Count(a, N);
    }
*/


/*@ requires N >= 0 && \valid_read(a + (0..N-1));
    
    assigns \nothing;
    
    ensures 0 <= \result <= N;
    ensures \result == Count(a, N);
*/
int count(int* a, int N)
{ 
    int countArr = 0;
    int i;
    /*@ loop invariant 0 <= i <= N;
        loop invariant 0 <= countArr <= i;
        loop invariant countArr == Count(a, i);
        loop assigns i, countArr;
        loop variant N - i;
    */
    for (i = 0; i < N; ++i)
    {
        if (i % 2 == 0 && a[i] % 2 != 0)
        {
            countArr++;
        }
    }

    return countArr;
}

int main() {
    // count numbers
    int N = 6;
    int* a;
    a = (int*) malloc(N*sizeof(int));
    //int a[N];
    //memcpy(a, (int[]) {23, 50, 61, 124, 562, 1000}, sizeof a);
    //a = {23, 50, 61, 124, 562, 1000};
    a[0] = 23;
    a[1] = 50;
    a[2] = 61;
    a[3] = 124;
    a[4] = 562;
    a[5] = 1000;
    int count_number = count(a, N);
    printf("count = %i\n", count_number);
    
    return 0;
}
