import java.lang.*;
import java.util.*;
import java.util.concurrent.ThreadLocalRandom;

public class Quick {

	private static int partition(Comparable[] a, int lo, int hi) {

		int i = lo, j = hi + 1;
		while (true) {

			while (less(a[++i], a[lo]))
				if (i == hi) break;

			while (less(a[lo], a[--j]))
				if (j == lo) break;

			if (i >= j) break;
			exch(a,i,j);

		}

		exch(a,lo,j);
		return j;
	}

	public static void sort(Comparable[] a) {
		// It's an overkill because if you have an array of thousands or millions of primitive values to sort,
		//  wrapping each one in an object just to do a sort is a bit costly, both in memory and in CPU.
		// Collections.shuffle(Arrays.asList(a));
 		shuffleArray(a); // We will use Durstenfeld shuffle
		sort(a, 0, a.length-1);
	}

	private static void sort(Comparable[] a, int lo, int hi) {
		if (hi <= lo) return;
		int j = partition(a, lo, hi);
		sort(a, lo, j-1);
		sort(a, j+1, hi);
	}

	public static void main(String[] args) {
		String[] a = new String[] {"S", "O", "R", "T", "E", "X", "A", "M", "P", "L", "E"};
		Quick.sort(a);
		for (Comparable c : a) {
			System.out.print(c + " ");
		}
		System.out.println();
	}

	private static boolean less(Comparable v, Comparable w) {
        	return v.compareTo(w) < 0;
    	}

	private static void exch(Object[] a, int i, int j) {
		Object swap = a[i];
		a[i] = a[j];
		a[j] = swap;
	}

	// Implementing Durstenfeld shuffle
	private static void shuffleArray(Comparable[] a) {
	    // If running on Java 6 or older, use `new Random()` on RHS here
	    Random rnd = ThreadLocalRandom.current();
	    for (int i = a.length - 1; i > 0; i--) {
	    	int index = rnd.nextInt(i + 1);
		exch(a,index,i);
	    }
	}
}
