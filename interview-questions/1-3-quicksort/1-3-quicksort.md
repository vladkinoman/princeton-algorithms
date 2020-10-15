# Interview Questions: Quicksort

## **Nuts and bolts**

**Question**. A disorganized carpenter has a mixed pile of `n` nuts and `n` bolts. The goal is to find the corresponding pairs of nuts and bolts. Each nut fits exactly one bolt and each bolt fits exactly one nut. By fitting a nut and a bolt together, the carpenter can see which one is bigger (but the carpenter cannot compare two nuts or two bolts directly). Design an algorithm for the problem that uses at most proportional to `n log n` compares (probabilistically).

**Answer**. I don't know...

> *Hint:* modify the quicksort partitioning part of quicksort.
>
> R*emark*: This [research paper](http://www.cs.ucla.edu/~rafail/PUBLIC/17.pdf) gives an algorithm that runs in n log^4 n time in the worst case.

## Selection in two sorted arrays

**Question**. Given two sorted arrays `a[]` and `b[]`, of lengths `n₁` and `n₂` and an integer `0 ≤ k < n₁ + n₂`, design an algorithm to find a key of rank `k`. The order of growth of the worst case running time of your algorithm should be `log n`, where `n = n₁ + n₂`.

- Version 1: `n1=n2` (equal length arrays) and `k=n/2` (median).
- Version 2: `k=n/2` (median).
- Version 3: no restrictions. 

> "A key of rank k" means a value that equal to k. For example, if k=2, then you need to find the element such as a[index]=2 where index is unknown.

**Answer**. Pseudocode:

```pseudocode
procedure select_in_two_sorted_arrays(a: array of values, b: array of values, n1: value, n2: value, k: value):
	index:= BinarySearch.rank(k, a)
	if index=-1 
		then 
			BinarySearch.rank(k, b)
	return index
```

Sorry, I don't get it. There may be an error in the question. It must be an exercise on QuickSelect but we can't use this algorithm because we have already sorted arrays and the running time of the algorithm should be `log n`. What is the point of the exercise if we can't use QuickSelect?​

> *Hint*: there are two basic approaches.
>
> - Approach A: Compute the median in *a*[] and the median in *b*[]. Recur in a subproblem of roughly half the size.
> - Approach B: Design a constant-time algorithm to determine whether *a*[*i*] is a key of rank *k*. Use this subroutine and binary search.
>
> Dealing with corner cases can be tricky.

## Decimal dominants

**Question**. Given an array with `n` keys, design an algorithm to find all values that occur more than `n/10` times. The expected running time of your algorithm should be linear.

**Answer**. Pseudocode:

```pseudocode
procedure get_array_of_decimal_dominants(arr: array of values):
	/* copy the array in order to do whatever we want */
	a:= copy_of_range(arr, 0, n-1)
	/* N in the best case (c < N), probably this is our case */
	Quick3Way.sort(a, 0, n-1)
	x:= a[0]
	appearances:= 1
	max_appearances:= 0
	p:= 0
	q:= 0
	for i:= 1 to n-1
		if a[i]=x
			then
				appearances:= appearances+1
		else
			then
				if appearances=n / 10 + 1 
					and appearances > max_appearances
					then
						p:= i-appearances
						q:= i-1
						max_appearances:= appearances
						/* reset, checking new subarray */
						x:= a[i]
						appearances:= 1
	if max_appearances=0 return nil
	return copy_of_range(a, p, q)
```

> *Hint:* determine the (n/10)^th largest key using quickselect and check if it occurs more than n/10 times.
>
> *Alternate solution hint:* use 9 counters.

So, I completed this exercise using the third approach. Quickselect and scanning take N (i.e. N+N), as well as my own algorithm without copying. So the only downside of my approach is the use of extra space. However, the algorithm has the same execution time, i.e. N for larger values.