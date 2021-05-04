/******************************************************************************
 *  Compilation:  javac OrderedArrayMaxPQ.java
 *  Execution:    java OrderedArrayMaxPQ
 *
 *  Priority queue implementation with an unsorted array.
 *
 ******************************************************************************/

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * The {@code OrderedArrayMaxPQ} class represents a max priority queue
 * of generic items.
 * It supports the usual <em>insert</em> and <em>deleteMax</em>
 * operations, along with methods for peeking the max item and
 * testing if the queue is empty.
 * <p>
 * This implementation uses a resizing array, which double the underlying array
 * when it is full and halves the underlying array when it is one-quarter full.
 * The <em>insert</em> operation takes linear time in the worst case.
 * The <em>delMax</em> operation takes constant amortized time.
 * The <em>max</em>, <em>size</em>, and <em>is-empty</em>
 * operations take constant time in the worst case.
 * <p>
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class OrderedArrayMaxPQ<Key extends Comparable<Key>>
        implements Iterable<Key>{
    // initial capacity of underlying resizing array
    private static final int INIT_CAPACITY = 8;
    private int n;     // number of elements
    private Key[] pq;  // elements

    /**
     * Initializes an empty priority queue.
     */
    OrderedArrayMaxPQ() {
        n = 0;
        pq = (Key[]) new Comparable[INIT_CAPACITY];
    }

    /**
     * Initializes a priority queue of initial capacity max.
     * @param max the initial capacity
     */
    OrderedArrayMaxPQ(int max) {
        n = max;
        pq = (Key[]) new Comparable[n];
    }

    /**
     * Initializes a priority queue from the keys in a[].
     * @param a the array of keys from which the priority queue
     * can be initialized
     */
    OrderedArrayMaxPQ(Key[] a) {
        n = a.length;
        pq = (Key[]) new Comparable[n];
        System.arraycopy(a, 0, pq, 0, n);
    }

    // resize the underlying array
    private void resize(int capacity) {
        assert capacity >= n;
        Key[] copy = (Key[]) new Comparable[capacity];
        for (int i = 0; i < n; i++) {
            copy[i] = pq[i];
        }
        pq = copy;
    }

    /**
     * Inserts the key into this priority queue.
     * @param key the key to insert
     */
    public void insert(Key key) {
        if (n == pq.length) resize(2*pq.length);   // double size of array if necessary
        for (int i = n; i >= 0; --i) {
            pq[i] = key;
            if (i == 0 || pq[i - 1].compareTo(pq[i]) < 0) {
                break;
            } else {
                Key tmp = pq[i - 1];
                pq[i - 1] = pq[i];
                pq[i] = tmp;
            }
        }
        n++;
    }

    /**
     * Returns the maximum in this priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key max() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        return pq[n-1];
    }

    /**
     * Removes the maximum in the priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key delMax() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        Key max = pq[n-1];
        pq[--n] = null;
        // shrink size of array if necessary
        if (n > 0 && n == pq.length/4) resize(pq.length/2);
        return max;
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
        OrderedArrayMaxPQ<String> pq = new OrderedArrayMaxPQ<>();
        pq.insert("to");
        pq.insert("be");
        pq.insert("or");
        pq.insert("not");
        pq.insert("to");
        pq.insert("be");
        String s1 = pq.delMax();
        String s2 = pq.delMax();
        String s3Peeked = pq.max();
        System.out.println(s1 + " " + s2 + " " + s3Peeked);
        pq.insert("why");
        String s4Why = pq.delMax();
        System.out.println(s4Why);
        pq.insert("thyself");
        System.out.println("Current state of the priority queue:");
        for (Object key: pq) {
            System.out.print(key + " ");
        }
        System.out.println();
    }

    @Override
    public Iterator<Key> iterator() {
        return new ArrayIterator();
    }

    private class ArrayIterator implements Iterator<Key> {
        private int i = 0;

        @Override
        public boolean hasNext() {
            return i < n;
        }

        @Override
        public Key next() {
            return pq[i++];
        }
    }
}
