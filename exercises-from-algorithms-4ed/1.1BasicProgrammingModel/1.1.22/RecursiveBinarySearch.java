import java.lang.System;
import java.util.Arrays;

import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.Locale;


public class RecursiveBinarySearch
{
	/****************************/
	// force Unicode UTF-8 encoding; otherwise it's system dependent
    private static final String CHARSET_NAME = "UTF-8";

    // assume language = English, country = US for consistency with StdIn
    private static final Locale LOCALE = Locale.US;

    // send output here
    private static PrintWriter out;

    // this is called before invoking any methods
    static {
        try {
            out = new PrintWriter(new OutputStreamWriter(System.out, CHARSET_NAME), true);
        }
        catch (UnsupportedEncodingException e) {
            System.out.println(e);
        }
    }
    /*******************************/

	public static int rank(int key, int[] a)
	{ return rank(key, a, 0, a.length - 1, 1);}

	private static int rank(int key, int[] a, int lo, int hi, int depth)
	{
		out.printf(LOCALE, "%"+ depth +"d %d\n", lo, hi);
		depth++;
		if (lo > hi) return -1; // base case
		int mid = lo + (hi - lo) / 2;
		if (a[mid] > key) return rank(key, a, lo, mid - 1, depth);
		else if (a[mid] < key) return rank(key, a, mid + 1, hi, depth);
		else return mid;
	}

	public static void main(String[] args) {
		int key = Integer.parseInt(args[0]);
		int[] a = new int [args.length - 1];
		for (int i = 0; i < a.length; i++)
			a[i] = Integer.parseInt(args[i+1]);

		Arrays.sort(a);
		for (int x : a) {
			System.out.print(x + " ");
		}
		System.out.println();

		//System.out.println(rank(key, a));
		out.printf(LOCALE, "index = %d",rank(key, a));
		out.flush();
	}
}