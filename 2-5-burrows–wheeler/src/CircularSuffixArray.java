import edu.princeton.cs.algs4.SuffixArrayX;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;

public class CircularSuffixArray {
    private int[] index;
    /**
     * Construct circular suffix array of s.
     * @param s input string
     */
    public CircularSuffixArray(String s) {
        if (s == null) {
            throw new IllegalArgumentException("the argument is null");
        }
        SuffixArrayX suffix = new SuffixArrayX(s);
        int n = s.length();
        index = new int[n];
        for (int i = 0; i < n; i++) {
            index[i] = suffix.index(i);
        }
    }
    
    /**
     * Returns length of s.
     * @return length of s
     */
    public int length() {
        return index.length;
    }

    /**
     * Returns index of ith sorted suffix.
     * @param i ith sorted suffix
     * @return index of ith sorted suffix.
     */
    public int index(int i) {
        if (i < 0 || i > index.length-1) {
            throw new IllegalArgumentException("the i argument is outside its prescribed range (between 0 and n-1)");
        }
        return index[i];
    }

    /**
     * Test client for {@code CircularSuffixArray} (required).
     * @param args
     */
    public static void main(String[] args) {
        In in = new In(args[0]);
        String s = in.readAll();
        CircularSuffixArray circularSuffix = new CircularSuffixArray(s);
        int n = circularSuffix.length();
        StdOut.println("length of string: " + n);
        for (int i = 0; i < n; i++) {
            StdOut.println("index[" + i + "] = " + circularSuffix.index(i));
        }
    }
}
