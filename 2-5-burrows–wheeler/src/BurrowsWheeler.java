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

import edu.princeton.cs.algs4.BinaryStdIn;
import edu.princeton.cs.algs4.BinaryStdOut;

/**
 * The {@code BurrowsWheeler} represents a data type for transforming a typical
 * English text file into a text file in which sequences of the same character occur
 * near each other many times. After this, move-to-front encoding and huffman compression
 * can be applied to fully implement the Burrows-Wheeler data compression algorithm.
 * <p>
 * This data type also supports inverse traformation for expansion.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BurrowsWheeler {
    private static final int R = 256;
    private static class QueueOfInts {
        private Node first;
        private Node last;

        private static class Node {
            private int item;
            private Node next;
        }

        private QueueOfInts() {
            first = null;
            last  = null;
        }

        /**
         * Returns true if this queue is empty.
         *
         * @return {@code true} if this queue is empty; {@code false} otherwise
         */
        private boolean isEmpty() {
            return first == null;
        }

        /**
         * Adds the item to this queue.
         *
         * @param  item the item to add
         */
        private void enqueue(int item) {
            Node oldlast = last;
            last = new Node();
            last.item = item;
            last.next = null;
            if (isEmpty()) first = last;
            else           oldlast.next = last;
        }

        /**
         * Removes and returns the item on this queue that was least recently added.
         *
         * @return the item on this queue that was least recently added
         */
        private int dequeue() {
            int item = first.item;
            first = first.next;
            if (isEmpty()) last = null;   // to avoid loitering
            return item;
        }
    }
    /**
     * Applies Burrows-Wheeler transform,
     * reading from standard input and writing to standard output.
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
     * Applies Burrows-Wheeler inverse transform,
     * reading from standard input and writing to standard output.
     */
    public static void inverseTransform() {
        int first = BinaryStdIn.readInt();
        QueueOfInts[] indeces = new QueueOfInts[R];
        int n = 0;
        while (!BinaryStdIn.isEmpty()) {
            char c = BinaryStdIn.readChar();
            if (indeces[c] == null) indeces[c] = new QueueOfInts();
            indeces[c].enqueue(n);
            n++;
        }
        int[] next = new int[n];
        int[] firstCol = new int[n];
        int j = 0;
        for (int i = 0; i < R; i++) {
            while (indeces[i] != null && !indeces[i].isEmpty()) {
                next[j] = indeces[i].dequeue();
                firstCol[j] = i;
                j++;
            }
        }
        int count = 0;
        int pos = first;
        while (count < n) {
            BinaryStdOut.write(firstCol[pos], 8);
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
