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
            BinaryStdOut.write(text.charAt(index == 0 ? 0 : index-1));
        }
        BinaryStdOut.close();
    }

    /**
     * apply Burrows-Wheeler inverse transform,
     * reading from standard input and writing to standard output
     */
    public static void inverseTransform() {

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
