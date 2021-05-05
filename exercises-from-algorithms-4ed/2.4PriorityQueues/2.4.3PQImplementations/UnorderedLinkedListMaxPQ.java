/******************************************************************************
 *  Compilation:  javac UnorderedLinkedListMaxPQ.java
 *  Execution:    java UnorderedLinkedListMaxPQ
 *
 *  Priority queue implementation with an unordered list.
 *
 ******************************************************************************/

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * The {@code UnorderedLinkedListMaxPQ} class represents a max priority queue
 * of generic items.
 * It supports the usual <em>insert</em> and <em>deleteMax</em>
 * operations, along with methods for peeking the max item and
 * testing if the queue is empty.
 * <p>
 * This implementation uses a doubly linked list.
 * The <em>max</em> and <em>delMax</em> operations take
 * linear time in the worst case.
 * The <em>insert</em>, <em>size</em>, and <em>is-empty</em>
 * operations take constant time in the worst case.
 * <p>
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class UnorderedLinkedListMaxPQ <Key extends Comparable<Key>>
    implements Iterable<Key> {
    private int n;
    private Node last;

    /**
     * Initializes an empty priority queue.
     */
    public UnorderedLinkedListMaxPQ() {
        n = 0;
        last = new Node();
    }

    private class Node {
        Key info;
        Node next;
        Node prev;
    }

    /**
     * Inserts the key into this priority queue.
     * @param key the key to insert
     */
    public void insert(Key key) {
        last.info = key;
        last.next = new Node();
        last.next.prev = last;
        last = last.next;
        n++;
    }

    /**
     * Returns the maximum in this priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key max() {
        if (isEmpty()) {
            throw new NoSuchElementException("Priority Queue underflow.");
        }
        Key maxval = last.prev.info;
        Node curr = last.prev.prev;
        while (curr != null) {
            if (maxval.compareTo(curr.info) < 0) maxval = curr.info;
            curr = curr.prev;
        }
        return maxval;
    }

    /**
     * Removes the maximum in the priority queue.
     * @return the maximum in this priority queue
     * @throws java.util.NoSuchElementException if this priority queue is empty
     */
    public Key delMax() {
        if (isEmpty()) {
            throw new NoSuchElementException("Priority Queue underflow.");
        }
        Node max = last.prev;
        Node curr = last.prev.prev;
        while (curr != null) {
            if (max.info.compareTo(curr.info) < 0) max = curr;
            curr = curr.prev;
        }
        Key maxval = max.info;
        if (max.prev != null) max.prev.next = max.next;
        max = null;
        --n;
        return maxval;
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

    private class LinkedListIterator implements Iterator<Key> {
        private Node curr = last.prev;
        public boolean hasNext() {
            return curr != null;
        }
        public Key next() {
            Key key = curr.info;
            curr = curr.prev;
            return key;
        }
    }

    @Override
    public Iterator<Key> iterator() {
        return new LinkedListIterator();
    }

    /**
     * Unit tests the {@code UnorderedArrayMaxPQ} data type.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        UnorderedLinkedListMaxPQ<String> pq = new UnorderedLinkedListMaxPQ<>();
        pq.insert("to");
        pq.insert("be");
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
    }
}
