/******************************************************************************
 *
 *  Execution (do it in the bin folder): 
 *  - transform: java BurrowsWheeler - < ../sample-data-files/abra.txt |
 *  java edu.princeton.cs.algs4.HexDump 16
 *  should be:
 *  00 00 00 03 41 52 44 41 52 43 41 41 41 41 42 42
 *  128 bits
 *  - inverseTransform: java BurrowsWheeler - < ../sample-data-files/abra.txt |
 *  java BurrowsWheeler +
 *  should be:
 *  ABRACADABRA!
 * 
 ******************************************************************************/
import java.lang.reflect.Array;
import java.util.Arrays;

import edu.princeton.cs.algs4.BinaryStdIn;
import edu.princeton.cs.algs4.BinaryStdOut;

/**
 * The {@code BurrowsWheeler} represents a data type for compressing.
 *
 * <p>
 * This implementation uses the {@code ...} data structure which is based on...
 * Construction takes time proportional to..
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BurrowsWheeler {

    /**
     * apply Burrows-Wheeler transform,
     * reading from standard input and writing to standard output
     */
    public static void transform() {
        String text = BinaryStdIn.readString();
        CircularSuffixArray suffix = new CircularSuffixArray(text);
        int i = 0;
        while (suffix.index(i) != 0) i++;
        BinaryStdOut.write(i);
        int n = text.length();
        for (i = 0; i < n; i++) {
            int index = suffix.index(i);
            BinaryStdOut.write(text.charAt(index == 0 ? n-1 : index-1));
        }
        BinaryStdOut.close();
    }

    /**
     * apply Burrows-Wheeler inverse transform,
     * reading from standard input and writing to standard output
     */
    public static void inverseTransform() {
        int first = BinaryStdIn.readInt();
        char[] lastCol = BinaryStdIn.readString().toCharArray();
        BinaryStdIn.close();
        char[] firstCol = lastCol.clone();
        Arrays.sort(firstCol);
        int n = firstCol.length;
        int[] next = new int[n];
        boolean[] marked = new boolean[n];
        for (int i = 0; i < n; i++) {
            int j = 0;
            while (j == i || marked[j] || firstCol[i] != lastCol[j]) j++;
            next[i] = j;
            marked[j] = true;
        }
        int count = 0;
        int pos = first;
        while (count < n) {
            BinaryStdOut.write(firstCol[pos]);
            pos = next[pos];
            count++;
        }
        BinaryStdOut.close();
    }

    /**
     * Test client for BurrowsWheeler.
     * if args[0] is "-", apply Burrows-Wheeler transform
     * if args[0] is "+", apply Burrows-Wheeler inverse transform
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        if      (args[0].equals("-")) BurrowsWheeler.transform();
        else if (args[0].equals("+")) BurrowsWheeler.inverseTransform();
    }
}
