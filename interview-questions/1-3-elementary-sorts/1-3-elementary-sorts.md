# Interview Questions: Elementary Sorts

## Intersection of two sets

**Question**. Given two arrays `a[]` and `b[]`, each containing `n` distinct 2D points in the plane, design a subquadratic algorithm to count the number of points that are contained both in array `a[]` and array `b[]`.﻿

> Subquadratic designates an algorithm whose complexity is `~o(n^2)`, using the little-`o` notation. This means that the complexity grows much slower than n^2. It could be anything from linear to almost quadratic.
>
> In layman's terms it's anything between linear and quadratic for instance n^2/logn.

**Answer**. 

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

Sorry, I couldn't find a solution to maintain first performance requirement. TODO find out what it is:

> *Hint*: 3-way partitioning.