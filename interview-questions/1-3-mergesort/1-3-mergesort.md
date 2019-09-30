# Interview Questions: Mergesort

## Merging with smaller auxiliary array

**Question**. Suppose that the subarray `a[0]` to `a[n−1]` is sorted and the subarray `a[n]` to `a[2∗n−1]` is sorted. How can you merge the two subarrays so that `a[0]` to `a[2∗n−1]` is sorted using an auxiliary array of length `n` (instead of `2n`)?

**Answer**.

```pseudocode
// standard merge
procedure merge(a : array of values, aux: array of values, lo: value, mid : value, hi: value):
	for k:=lo to hi
		aux[k] = a[k];
	end for
	i:= lo;
	j:= mid+1;
	for k:= lo to hi
		if      i > mid 
			then 
				a[k] := aux[j];
				j:=j+1;
		else if j > hi 
			then
            	a[k] := aux[i];
                i:=i+1;
        else if less(aux[j], aux[i])
        	then
        		a[k] := aux[j];
        		j:=j+1;
        else
        	then
            	a[k] := aux[i];
            	i:= i+1;
        end if
 	end for
```

Thoughts:

1. We should make `merge` function recursive. In that way, we can divide each time our array into two subarrays so that they get into a halved `auxillary` array.
2. Base case: only two elements left in the `a[]` array (for instance, `0` and `n`). Meanwhile, `aux[]` has only 1 element.T

TODO: complete this later.

> *Hint*:  copy only the left half into the auxiliary array.

## Counting inversions

**Question**. An inversion in an array `a[]` is a pair of entries `a[i]` and `a[j]` such that `i < j` but `a[i] >a[j]`. Given an array, design a linearithmic algorithm to count the number of inversions.

**Answer**. Code:

```pseudocode
procedure merge(a : array of values, aux: array of values, lo: value, mid : value, hi: value):
	for k:=lo to hi
		aux[k] = a[k];
	end for
	i:= lo;
	j:= mid+1;
	inv_count:=0;
	for k:= lo to hi
		if      i > mid 
			then 
				a[k] := aux[j];
				j:=j+1;
		else if j > hi 
			then
            	a[k] := aux[i];
                i:=i+1;
        else if less(aux[j], aux[i])
        	then
        		a[k] := aux[j];
        		j:=j+1;
        		inv_count:=inv_count + mid - i + 1;
        else
        	then
            	a[k] := aux[i];
            	i:= i+1;
        end if
 	end for
 	return inv_count;
 
procedure sort(a: array of values, aux: array of values, lo: value, hi: value):
	inv_count:=0;
	if lo <= hi return inv_count;
	mid:= lo + (hi - lo)/2;
	inv_count:= inv_count + sort(a, aux, lo, mid);
	inv_count:= inv_count + sort(a, aux, mid+1, hi);
	inv_count:= inv_count + merge(a, aux, lo, hi);
	return inv_count;

// +N
procedure count_inversions(input_array: array of values):
	N:= input_array.length;
	for i=0 to N
		a[i] = input_array[i];
	end for
	array aux[] = new array [N];
	return sort(a, aux, 0, N);
```

I think, this algorithm implies what the hint means.

> *Hint*: count while mergesorting.

## Shuffling a linked list

**Question**. Given a singly-linked list containing `n` items, rearrange the items uniformly at random. Your algorithm should consume a logarithmic (or constant) amount of extra memory and run in time proportional to `n log` in the worst case.

**Answer**. Thoughts:

1. We should use the bottom-up mergesort because of the list.
2. `StdRandom.uniform` method will help us to generate a number uniformly at random.
3. The simple Knuth shuffle doesn't work here because we manipulate the singly-linked list. It would be very hard to control links of items.

(After reading the hint below) Well, I expected that this will be the most difficult question :)

> *Hint*: design a linear-time subroutine that can take two uniformly shuffled linked lists of sizes n_1 and n_2 and combined them into a uniformly shuffled linked lists of size n_1 + n_2.