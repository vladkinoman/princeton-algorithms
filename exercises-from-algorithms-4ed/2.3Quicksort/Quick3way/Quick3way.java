import java.util.*;
import java.util.concurrent.ThreadLocalRandom;

public class Quick3way {

	// this class should not be instantiated
	private Quick3way() { }

	public static void sort(Comparable[] a) {
		shuffle(a);
		sort(a, 0, a.length - 1);
	}

	private static void sort(Comparable[] a, int lo, int hi) {
		if (hi <= lo) return;
		int lt = lo, gt = hi;
		Comparable v = a[lo];
		int i = lo;
		while (i <= gt) {
			int cmp = a[i].compareTo(v);
			if (cmp < 0) exch(a, i++, lt++);
			else if (cmp > 0) exch(a, i, gt--);
			else i++;
		}
		// if you comment the next two lines, you can sort the
		// array which containts just two distinct key values
		sort(a, lo, lt-1);
		sort(a, gt+1, hi);
	}

	private static void exch(Comparable[] a, int i, int j) {
		Comparable swap = a[i];
		a[i] = a[j];
		a[j] = swap;
	}

	public static void main(String[] args) {
		String[] a = new String[] {"R", "B", "W", "W", "R", "W", "B", "R", "R", "W", "B", "R"};
		// here is the test case to check quicksort for two distinct key values
		// comment the lines in the function sort(a, lo, hi)
		//String[] a = new String[] {"R", "R", "W", "W", "R", "W", "R", "R", "R", "W", "R", "R"};
                sort(a);
                for (Comparable c : a) {
                        System.out.print(c + " ");
                }
                System.out.println();

	}

	private static void shuffle(Comparable[] a) {
		Random rnd = ThreadLocalRandom.current();
		for (int i = a.length - 1; i > 0; i--) {
			int r = rnd.nextInt(i+1);
			exch(a, i, r);
		}
	}
}
