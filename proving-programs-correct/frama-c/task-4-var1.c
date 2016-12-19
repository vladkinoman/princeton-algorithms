#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*@
    axiomatic count_axioms
    {
        logic integer count{L} (int* a, integer N)
            reads a[0..N-1];
        
        axiom count_empty{L}:
            \forall int* a, integer N;
                N <= 0 ==> count(a, N) == 0;

        axiom count_add{L}:
            \forall int* a, integer N;
               N % 2 == 0 && a[N] % 2 != 0 
               ==> count(a, N + 1) == count(a, N) + 1;
        
        axiom count_pass{L}:
            \forall int* a, integer N;
               !(N % 2 == 0 && a[N] % 2 != 0) 
               ==> count(a, N + 1) == count(a, N);
    }
*/


/*@ 
    requires N >= 0 && \valid(a + (0..N-1));
    
    assigns \nothing;
    
    ensures 0 <= \result <= N;
    ensures \result == count(a, N);
*/
int count(int* a, int N)
{ 
    int x = 0;
    int i;
    /*@ loop invariant 0 <= i <= N;
        loop invariant 0 <= x <= i;
        loop invariant x == count(a, i);
        loop assigns i, x;
        loop variant N - i;
    */
    for (i = 0; i < N; i++)
    {
        if (i % 2 == 0 && a[i] % 2 != 0)
        {
            x = x + 1;
        }
    }

    return x;
}

int main() {

    int N = 10;
    int a[N];
    memcpy(a, (int []) {11, 20, 33, 40, 55, 60, 77, 80, 99, 100}, sizeof a);
    int count_number = count(a, N);
    printf("count = %i\n", count_number);
    
    return 0;
}
