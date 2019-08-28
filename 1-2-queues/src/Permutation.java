
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

/**
 The {@code Permutation} client program takes an integer k as a command-line argument;
 * reads a sequence of strings from standard input using StdIn.readString();
 * and prints exactly k of them, uniformly at random.
 * Print each item from the sequence at most once.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 *
 */
public class Permutation {

    /**
     * Unit tests the {@code Deque} or {@code RandomizedQueue} data types.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {

        RandomizedQueue<String> randqueue = new RandomizedQueue<>();
        while (!StdIn.isEmpty())
            randqueue.enqueue(StdIn.readString());

        int k = Integer.parseInt(args[0]);
        if (k < 0 || k > randqueue.size())
            throw new IllegalArgumentException();

        for (String s : randqueue) {
            StdOut.println(s);
            if (--k == 0) break;
        }

    }
}
