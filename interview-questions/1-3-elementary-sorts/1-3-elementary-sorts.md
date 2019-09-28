# Interview Questions: Elementary Sorts

## Intersection of two sets

**Question**. Given two arrays `a[]` and `b[]`, each containing `n` distinct 2D points in the plane, design a subquadratic algorithm to count the number of points that are contained both in array `a[]` and array `b[]`.﻿

> Subquadratic designates an algorithm whose complexity is `~o(n^2)`, using the little-`o` notation. This means that the complexity grows much slower than n^2. It could be anything from linear to almost quadratic.
>
> In layman's terms it's anything between linear and quadratic for instance n^2/logn.

**Answer**. The right answer is at the bottom of the answer paragraph.

Brute-force solution which is similar to Selection Sort (assume that points are distinct):

```Java
for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++)
        if (a[i].x() == b[j].x() && a[i].y() == b[j].y())
            count++;
```

The main problem with that solution is that it takes time proportional to `~N^2` which is bad for us cause we need subquadratic algorithm.

New algorithm (assuming that point are distinct):

```java
int count = 0; 
Shell.sort(a); // ~ N^{3/2}
Shell.sort(b); // ~ N^{3/2}

int j = 0;
for (int i = 0; i < N; i++) {
    for (; j < N && a[i].x() >= b[j].x()
           && (a[i].x() != b[j].x() || a[i].y() >= b[j].y()); j++) {
        if (a[i].x() == b[j].x() && a[i].y() == b[j].y())
            count++;
    }
}
return count;
```

The running time of this algorithm is `~ 2N^{3/2}` in the worst case.

Improved solution with Binary Search (again, I assume that all points in the arrays are distinct):

```java
int count = 0;
int N = a.length;
Shell.sort(b);

for (int i = 0; i < N ; i++)
    if (BinarySearch.rank(a[i], b) > -1)
        count++

return count;
```

This algorithm takes time proportional to `~N^{3/2}` in the worst case which is great! :)

Conclusion: the version with Binary Search is my answer on this question.

Attempting to improve the second algorithm according to [this](https://stackoverflow.com/questions/12863904/algorithm-to-find-intersection-of-two-sets-without-using-any-data-structure#answer-12864031) answer after getting the hint below:

```Java
/* Using next class from the algs4.jar
public final class edu.princeton.cs.algs4.Point2D implements java.lang.Comparable<edu.princeton.cs.algs4.Point2D> {
  ...
  public double x();
  public double y();
  ...
}
*/
int count = 0; 
Shell.sort(a); // ~ N^{3/2}
Shell.sort(b); // ~ N^{3/2}

for (int i = 0, j = 0; i < N && j < N; ) {
    if 	    (a[i].x() > b[j].x()) j++;
    else if (a[i].x() < b[j].x()) i++;
    else {
        if 		(a[i].y() > b[j].y()) j++;
        else if (a[i].x() < b[j].x()) i++;
        else {
           // element is in intersection
           count++;
           i++;
           j++;  
        }
    }
}
return count;
```

The running time of this algorithm is `~ 2N^{3/2}` (`+8N` compares) in the worst case which is better than quadratic time.

> *Hint*: shellsort (or any other subquadratic sort).

## Permutation

**Question**. Given two integer arrays of size `n`, design a subquadratic algorithm to determine whether one is a permutation of the other. That is, do they contain exactly the same entries but, possibly, in a different order.

**Answer**. I assume that array is small enough to make Shellsort effective:

```Java
Shell.sort(a); // ~ N^{3/2}
Shell.sort(b); // ~ N^{3/2}
int N = a.length;
for (int i = 0; i < N; i++) // N
    if (a[i] != b[i])
        return false;
return true;
```

The running time of this algorithm is `~2N^{3/2}` which is better than quadratic algorithm.

> *Hint*: sort both arrays.

## Dutch national flag

**Question**. Given an array of `n` buckets, each containing a red, white, or blue pebble, sort them by color. The allowed operations are:

- `swap(i, j)`: swap the pebble in bucket `i` with the pebble in bucket `j`.
- `color(i)`: determine the color of the pebble in bucket `i`.

The performance requirements are as follows:

- At most `n` calls to `color()`.
- At most `n` calls to `swap()`.
- Constant extra space.

**Answer**. Let's set some designations: `1` will be red, `0` will be white, `-1` will be blue. Code:

```pseudocode
procedure int find_and_swap_in_remaining_part(i, color):
for j:=i+1 to N
    if color(i) = 1
    	then
        	swap(i, j);
        	return j;
    end if
end for
return -1;

procedure void sort_array_of_buckets():
color_number := 0;
for i:=0 to n-1
	color_number := color(i);
	if color_number = 1 // red
		then; // we do nothing
	else if color_number = 0 // white
		then find_and_swap_in_remaining_part(i, 1);
	else // blue
		// find red pebble and swap with it
		if find_and_swap_in_remaining_part(i, 1) < 0
			// if there is no red, then find white
			then 
				if find_and_swap_in_remaining_part(i, 0) < 0
				 	// if there is no white, then stop the algorithm
				 	then return;
				end if
		end if
	end if
end for
return	
```

In this way, I can guarantee that only two performance requirements will be maintained:

- At most `n` calls to `swap()`.
- Constant extra space.

Sorry, I couldn't find a solution to maintain first performance requirement.

*3-way partitioning* (according to this [WIKI](https://www.wikiwand.com/en/Dutch_national_flag_problem) page):

The following pseudocode for three-way partitioning assumes zero-based array indexing. It uses three indices `i`, `j` and `n`, maintaining the invariant that `i ≤ j`. In this example `mid` is equal to `0` which corresponds to `white` color of a pebble.

`n` holds the lower boundary of numbers greater than `mid`.

`j` is the position of the number under consideration. And `i` is the boundary for the numbers less than the mid value.

```pseudocode
procedure three_way_partition(A : array of values, mid : value):
    i:= 0;
    j:= 0;
    n:= size of A - 1;

    while j <= n:
        if color(j) < mid:
            swap(i, j);
            i:= i + 1;
            j:= j + 1;
        else if color(j) > mid:
            swap(j, n);
            n:= n - 1;
        else:
            j:= j + 1;
```

Note that `j` will be greater than `i` only if the `mid` is hit.

> *Hint*: 3-way partitioning.