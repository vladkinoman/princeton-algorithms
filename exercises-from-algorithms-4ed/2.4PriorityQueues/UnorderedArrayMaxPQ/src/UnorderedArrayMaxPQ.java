/******************************************************************************
 *  Compilation:  javac UnorderedArrayMaxPQ.java
 *  Execution:    java UnorderedArrayMaxPQs
 *
 *  Priority queue implementation with an unsorted array.
 *
 *  Limitations
 *  -----------
 *   - no array resizing
 *   - no iterating
 *
 ******************************************************************************/

import java.util.NoSuchElementException;

/**
 * The {@code UnorderedArrayMaxPQ} class represents a max priority queue
 * of generic items.
 * It supports the usual <em>insert</em> and <em>deleteMax</em>
 * operations, along with methods for peeking the max item,
 * testing if the queue is empty.
 * <p>
 * This implementation uses a resizing array, which double the underlying array
 * when it is full and halves the underlying array when it is one-quarter full.
 * The <em>delMax</em> operation takes linear time.
 * The <em>insert</em>, <em>max</em>, <em>size</em>, and <em>is-empty</em>
 * operations takes constant time in the worst case.
 * <p>
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class UnorderedArrayMaxPQ<Key extends Comparable<Key>> {
    private int n;     // number of elements
    private Key[] pq;  // elements

    /**
     * Initializes an empty priority queue.
     */
    UnorderedArrayMaxPQ() {
        n = 0;
        pq = (Key[]) new Comparable[1];
    }

    /**
     * Initializes a priority queue of initial capacity max.
     * @param max the initial capacity
     */
    UnorderedArrayMaxPQ(int max) {
        n = max;
        pq = (Key[]) new Comparable[n];
    }

    /**
     * Initializes a priority queue from the keys in a[].
     * @param a the array of keys from which the priority queue
     * can be initialized
     */
    UnorderedArrayMaxPQ(Key[] a) {
        n = a.length;
        pq = (Key[]) new Comparable[n];
        for (int i = 0; i < n; i++) {
            pq[i] = a[i];
        }
    }

    /**
     * Inserts the key into this priority queue.
     * @param key the key to insert
     */
    public void insert(Key key) {
        pq[n++] = key;
    }

    /**
     * Returns the maximum in this priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key max() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        int max = 0;
        for (int i = 1; i < n; i++) {
            if (less(max, i)) max = i;
        }
        return pq[max];
    }

    /**
     * Removes the maximum in the priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key delMax() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        int max = 0;
        for (int i = 1; i < n; i++) {
            if (less(max, i)) max = i;
        }

        Key tmp = pq[max];
        pq[max] = pq[n-1];
        pq[--n] = null;

        return tmp;
    }

    // compare two items by indices
    private boolean less(int i, int j) {
        return pq[i].compareTo(pq[j]) < 0;
    }

    /**
     * Returns the number of items in this priority queue.
     * @return the number of items in this priority queue.
     */
    public int size() {
        return n;
    }

    /**
     * Checks whether this pq is empty.
     * @return true if this queue is empty; false otherwise
     */
    public boolean isEmpty() {
        return n == 0;
    }

    /**
     * Unit tests the {@code UnorderedArrayMaxPQ} data type.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        UnorderedArrayMaxPQ<String> pq = new UnorderedArrayMaxPQ<String>(
                new String[]{"to", "be", "or", "not", "to", "be"}
        );
        String s1 = pq.delMax();
        String s2 = pq.delMax();
        String s3Peeked = pq.max();
        System.out.println(s1 + " " + s2 + " " + s3Peeked);
        pq.insert("why");
        String s4Why = pq.delMax();
        System.out.println(s4Why);
    }
}