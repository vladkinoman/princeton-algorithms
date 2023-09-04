/******************************************************************************
 *
 *  Execution: 
 *  - encoding: java MoveToFront - < ../sample-data-files/abra.txt |
 *  java edu.princeton.cs.algs4.HexDump 16
 *  should be:
 *  41 42 52 02 44 01 45 01 04 04 02 26
 *  96 bits
 *  - decoding: java MoveToFront - < ../sample-data-files/abra.txt | java MoveToFront +
 *  should be:
 *  ABRACADABRA!
 * 
 ******************************************************************************/

import edu.princeton.cs.algs4.BinaryStdIn;
import edu.princeton.cs.algs4.BinaryStdOut;

public class MoveToFront {
    private static final int R = 256;
    private static class Node {
        private Node next;
        private Node prev;
        private int c;
    }

    /**
     * apply move-to-front encoding, reading from standard input and writing to standard outputs
     */
    public static void encode() {
        Node first = new Node();
        Node node = first;
        for (int i = 0; i < R; i++) {
            node.c = i;
            if (i != R-1) {
                node.next = new Node();
                node.next.prev = node;
            }
            node = node.next;
        }
        node = first;
        while (!BinaryStdIn.isEmpty()) {
            char c = BinaryStdIn.readChar();
            int index = 0;
            while (node.c != c) {
                node = node.next;
                index++;
            }
            BinaryStdOut.write(index, 8);
            if (node != first) {
                node.prev.next = node.next;
                if (node.next != null) {
                    node.next.prev = node.prev;
                }
                node.prev = null;
                node.next = first;
                first.prev = node;
                first = node;
            }
        }
        BinaryStdOut.close();
    }

    /**
     * apply move-to-front decoding, reading from standard input and writing to standard output
     */
    public static void decode() {
        Node first = new Node();
        Node node = first;
        for (int i = 0; i < R; i++) {
            node.c = i;
            if (i != R-1) {
                node.next = new Node();
                node.next.prev = node;
            }
            node = node.next;
        }
        node = first;
        while (!BinaryStdIn.isEmpty()) {
            int index = BinaryStdIn.readChar();
            int currIndex = 0;
            while (index != currIndex) {
                node = node.next;
                currIndex++;
            }
            BinaryStdOut.write(node.c);
            if (node != first) {
                node.prev.next = node.next;
                if (node.next != null) {
                    node.next.prev = node.prev;
                }
                node.prev = null;
                node.next = first;
                first.prev = node;
                first = node;
            }
        }
        BinaryStdOut.close();
    }

    /**
     * Test client for {@code MoveToFront}.
     * <p>
     * if args[0] is "-", apply move-to-front encoding
     * if args[0] is "+", apply move-to-front decoding
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        if      (args[0].equals("-")) MoveToFront.encode();
        else if (args[0].equals("+")) MoveToFront.decode();
    }
}
