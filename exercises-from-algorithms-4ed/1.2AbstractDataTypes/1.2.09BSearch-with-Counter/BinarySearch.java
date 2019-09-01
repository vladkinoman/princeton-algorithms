import java.lang.System;

public class BinarySearch
{
	public static int rank(int[] a, int key, Counter counter)
	{
		int lo = 0;
		int hi = a.length - 1;

		while(lo <= hi) {
			int mid = lo + (hi - lo) / 2;
			counter.increment();
			if     (a[mid] > key) hi = mid - 1;
			else if(a[mid] < key) lo = mid + 1;
			else return mid;
		}

		return -1; 
	}

	public static void main(String[] args) {
		int[] a = {1, 5, 7, 8, 10, 23, 44, 67, 81};
		int[] keys = new int[args.length];
		for (int i = 0; i < keys.length ; i++)
			keys[i] = Integer.parseInt(args[i]);
		Counter counter = new Counter("Count of checked keys");
		for (int i = 0; i < keys.length; i++)
			rank(a, keys[i], counter);
		System.out.println(counter);
	}
}