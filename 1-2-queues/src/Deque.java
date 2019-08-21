
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import java.util.Iterator;
import java.util.NoSuchElementException;
// also you can use java.lang

/**
 The {@code Deque} class represents a deque of generic items.
 *  A randomized queue is similar to a stack or queue,
 *  except that it supports adding and removing items
 *  from either the front or the back of the data structure,
 *  and iterating over the items in order from front to back.
 *  <p>
 *  This implementation uses a ... with a ... .
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 *
 * @param <Item> the generic type of an item in this deque
 */
public class Deque<Item> implements Iterable<Item> {
    /**
     * Beginning of deque.
     */
    private Node first;

    /**
     * Ending of deque.
     */
    private Node last;
    /**
     * Number of items in deque.
     */
    private int count;

    /**
     * Helper linked list class.
     */
    private class Node {
        private Node next;
        private Node prev;
        private Item item;
    }
    /**
     * Constructs an empty deque.
     */
    public Deque() {
        first = null;
        last = null;
    }

    /**
     * Returns true if the deque is empty.
     *
     * @return {@code true} if the deque is empty;
     *         {@code false} otherwise
     */
    public boolean isEmpty() {
        return first == null;
    }

    /**
     * Returns the number of items on the deque.
     *
     * @return the number of items on the deque
     */
    public int size() {
        return count;
    }

    /**
     * Adds the item to the front.
     *
     * @param item the item which is added to the front
     * @throws IllegalArgumentException if the client calls addFirst() with a {@code null} argument
     */
    public void addFirst(Item item) {
        if (item == null) throw new IllegalArgumentException();
        Node newNode = new Node();
        newNode.item = item;
        newNode.next = first;
        newNode.prev = null;
        first = newNode;
        count++;
    }

    /**
     * Adds the item to the back.
     *
     * @param item the item which is added to the back
     * @throws IllegalArgumentException if the client calls addLast() with a {@code null} argument
     */
    public void addLast(Item item) {
        if (item == null) throw new IllegalArgumentException();
        Node newNode = new Node();
        newNode.item = item;
        newNode.next = null;
        newNode.prev = last;
        last = newNode;
        count++;
    }

    /**
     * Removes and returns the item from the front.
     *
     * @return the item which is removed from the front
     * @throws NoSuchElementException if the client calls removeFirst() when the deque is empty
     */
    public Item removeFirst() {
        if (isEmpty()) throw new NoSuchElementException();
        Item removingItem = first.item;
        first = first.next;
        first.prev = null;
        count--;
        return removingItem;
    }

    /**
     * Removes and returns the item from the back
     *
     * @return the item which is removed from the front
     * @throws NoSuchElementException if the client calls removeLast() when the deque is empty
     */
    public Item removeLast() {
        if (isEmpty()) throw new NoSuchElementException();
        Item removingItem = last.item;
        last = last.prev;
        last.next = null;
        count--;
        return removingItem;
    }

    /**
     * Returns an iterator that iterates over the items in order from front to back.
     *
     * @return an iterator that iterates over the items in order from front to back
     */
    public Iterator<Item> iterator() {
        return new DoubleLinkedListIterator();
    }

    private class DoubleLinkedListIterator implements Iterator<Item> {

        private Node current = first;

        @Override
        public boolean hasNext() {
            return current != null;
        }

        @Override
        public Item next() {
            if (isEmpty()) throw new NoSuchElementException();
            Item currItem = current.item;
            current = current.next;
            return currItem;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Unit tests the {@code Deque} data type. (required)
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {

    }
}
