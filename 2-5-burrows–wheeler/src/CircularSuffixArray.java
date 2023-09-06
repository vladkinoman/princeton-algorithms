import java.util.Arrays;
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
        char[] doubleds = s.concat(s).toCharArray();
        int n = s.length();
        Suffix[] suffixes = new Suffix[n];
        for (int i = 0; i < n; i++) {
            suffixes[i] = new Suffix(doubleds, i);
        }
        Arrays.sort(suffixes);
        index = new int[n];
        for (int i = 0; i < n; i++) {
            index[i] = suffixes[i].index;
        }
    }

    private static class Suffix implements Comparable<Suffix> {
        private final char[] text;
        private final int index;

        private Suffix(char[] text, int index) {
            this.text = text;
            this.index = index;
        }
        private char charAt(int i) {
            return text[index + i];
        }
        public int compareTo(Suffix that) {
            if (this == that) return 0;  // optimization
            int n = this.text.length / 2;
            for (int i = 0; i < n; i++) {
                if (this.charAt(i) < that.charAt(i)) return -1;
                if (this.charAt(i) > that.charAt(i)) return +1;
            }
            return 0;
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
