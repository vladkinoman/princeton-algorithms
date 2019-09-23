# Interview Questions: Analysis of Algorithms

## 3-SUM in quadratic time

**Question**. Design an algorithm for the 3-SUM problem that takes time proportional to n^2 in the worst case. You may assume that you can sort the n integers in time proportional to n^2 or better.

**Answer**. There is a ThreeSumFast version of the algorithm which we considered at the lecture. It takes time proportional to N^2*logN. It is based on Binary Search algorithm which searches perfect (when sum equals zero) element for the pair of elements a[i] and a[j]. 
Scientists say that there is a version of N^2 algorithm but nobody knows if there is a faster version.

>  *Hint*: given an integer x and a sorted array a[] of n distinct integers, design a linear-time algorithm to determine if there exists two distinct indices i and j such that a[i]+a[j]==x. 

## Search in a bitonic array

**Question**. An array is bitonic if it is comprised of an increasing sequence of integers followed immediately by a decreasing sequence of integers. Write a program that, given a bitonic array of n distinct integer values, determines whether a given integer is in the array.

- Standard version: Use ∼3lgn compares in the worst case.

  > Simple solution - [1].

- Signing bonus: Use ∼2lgn compares in the worst case (and prove that no algorithm can guarantee to perform fewer than ∼2lgn compares in the worst case).

  > Clever solution - [2]. We don't need to find the maximum. We can do these things:
  >
  > ```
  > if key > a[mid]:
  >     search in one side only
  > else:
  >     search in both side
  > ```
  >
  > Notice that the search function above is always binary search, which means we will solve this problem using recursion. At the end of the recursion, segment of the array will be monotonous. Thus, we can use binary search in the bitonic array.

**Answer**. I built an algorithm for the standard version (3lgn compares in the worst case): find the bitonic point (max), do binary search on the left side, do binary search on the right side. Didn't know that is ~3lgn (lgn for max, lgn for ascending bs, and lgn for descending bs). 

After that I wanted to get signing bonus. I thought about binary search, but I came up with an algorithm which someone call as "Front and Back search algorithm" [3]. It has ~N/2 compares in the worst case which is great for small numbers, but bad for big ones. In summary, N/2 is worse than lg N for big N. Code:

```Java
public static boolean isItemExistsInBitonicArray(int key, int[] a) {
    int N = a.length;
    for (int i = 0; i <= N-i-1 ; i++)
    	if (a[i] == key && a[N-i-1] == key) return true;
    return false;
}
```

> *Hints*: Standard version. First, find the maximum integer using ∼1lgn compares—this divides the array into the increasing and decreasing pieces.
>
> Signing bonus. Do it without finding the maximum integer.

## Links

1. [Find an element in Bitonic array](https://www.geeksforgeeks.org/find-element-bitonic-array/)

2. [Bitonic search in time ~2logN](https://stackoverflow.com/questions/19372930/given-a-bitonic-array-and-element-x-in-the-array-find-the-index-of-x-in-2logn/21697488#answer-24098821)

3. [Front and Back Search in unsorted array](https://www.geeksforgeeks.org/front-and-back-search-in-unsorted-array/)

