/******************************************************************************
 *  Compilation:  javac BinaryHeapMaxPQ.java
 *  Execution:    java BinaryHeapMaxPQ
 *
 *  Priority queue implementation based on binary heap.
 *
 ******************************************************************************/

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * The {@code BinaryHeapMaxPQ} class represents a max priority queue
 * of generic items.
 * It supports the usual <em>insert</em> and <em>deleteMax</em>
 * operations, along with methods for peeking the max item and
 * testing if the queue is empty.
 * <p>
 * This implementation uses a resizing array, which double the underlying array
 * when it is full and halves the underlying array when it is one-quarter full.
 * The <em>insert</em> and <em>delMax</em> operations take logarithmic
 * time in the worst case.
 * The <em>max</em>, <em>size</em>, and <em>is-empty</em>
 * operations take constant time in the worst case.
 * <p>
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BinaryHeapMaxPQ<Key extends Comparable<Key>>
        implements Iterable<Key>{
    // initial capacity of underlying resizing array
    private static final int INIT_CAPACITY = 8;
    private Key[] pq; // elements (the zero element is empty and unused)
    private int n;    // number of elements (inc. including the zero element)

    /**
     * Initializes an empty priority queue.
     */
    BinaryHeapMaxPQ() {
        n = 0;
        pq = (Key[]) new Comparable[INIT_CAPACITY];
    }

    /**
     * Initializes a priority queue of initial capacity max.
     * @param max the initial capacity
     */
    BinaryHeapMaxPQ(int max) {
        n = 0;
        pq = (Key[]) new Comparable[max+1];
    }

    /**
     * Initializes a priority queue from the keys in a[].
     * @param a the array of keys from which the priority queue
     * can be initialized
     */
    BinaryHeapMaxPQ(Key[] a) {
        pq = (Key[]) new Comparable[a.length+1];
        for (int i = 0; i < a.length; i++) {
            insert(a[i]);
        }
    }

    /**
     * Inserts the key into this priority queue.
     * @param key the key to insert
     */
    public void insert(Key key) {
        if (n == pq.length) resize(pq.length * 2);
        pq[++n] = key;
        promote(n);
    }

    // makes the ith element to float out
    private void promote(int i) {
        while (i > 1 && pq[i].compareTo(pq[i/2]) > 0) {
            swap(i, i/2);
            i /= 2;
        }
    }

    /**
     * Removes the maximum in the priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key delMax() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        Key max = pq[1];
        swap(1, n);
        pq[n--] = null; // prevent loitering
        demote(1);
        // shrink size of array if necessary
        if (n > 1 && n == pq.length/4) resize(pq.length/2);
        return max;
    }

    // sinks the ith item
    private void demote(int i) {
        while (2*i <= n) {
            int j = 2*i;
            // "j < n" prevents checking the second item if it doesn't exist
            if (j < n && pq[j].compareTo(pq[j+1]) < 0) j++; // 2nd child is bigger
            // do nothing because the parent is greater than its children
            if (pq[i].compareTo(pq[j]) > 0) break;
            swap(i, j);
            i = j;
        }
    }

    public Key max() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        return pq[1];
    }

    /**
     * Returns the number of items in this priority queue.
     * @return the number of items in this priority queue.
     */
    public int size() {
        return n;
    }

    /**
     * Checks whether the priority queue is empty.
     * @return true if this queue is empty; false otherwise
     */
    public boolean isEmpty() {
        return n == 0;
    }

    private void resize(int size) {
        Key[] new_pq = (Key[]) new Comparable[size];
        System.arraycopy(pq, 0, new_pq, 0, n);
        pq = new_pq;
    }

    private void swap(int i, int j) {
        Key tmp = pq[i];
        pq[i] = pq[j];
        pq[j] = tmp;
    }

    private class ArrayIterator implements Iterator<Key> {
        private int i = 0;

        @Override
        public boolean hasNext() {
            return i < n;
        }

        @Override
        public Key next() {
            return pq[++i];
        }
    }

    @Override
    public Iterator<Key> iterator() {
        return new ArrayIterator();
    }

    /**
     * Finds min in linear time.
     * @return min in this pq
     * @throws NoSuchElementException if the pq is empty
     */
    public Key min() {
        if (isEmpty()) throw new NoSuchElementException("Priority Queue underflow");
        // This is my solution of min. It uses at most n/2 compares.
        //  In essence, we are iterating over the leaves of the tree.
        // The correct solution is to use an extra instance variable
        // that points to the minimum item. Update it after each call to insert().
        // Reset it to null if the priority queue becomes empty.
        Key min = pq[n];
        for (int i = n/2 + 1; i < n; i++) {
            if (min.compareTo(pq[i]) > 0) min = pq[i];
        }
        return min;
    }

    /**
     * Unit tests the {@code BinaryHeapMaxPQ} data type.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        BinaryHeapMaxPQ<String> pq = new BinaryHeapMaxPQ<>();
        pq.insert("to");
        pq.insert("ba");
        pq.insert("or");
        pq.insert("not");
        pq.insert("to");
        pq.insert("be");
        pq.insert("thyself");
        pq.delMax();
        System.out.println("Current state of the priority queue:");
        for (Object key: pq) {
            System.out.print(key + " ");
        }
        System.out.println();
        System.out.println("min = " + pq.min());
    }
}
