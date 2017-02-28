import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

import java.util.Iterator;

public class Deque<Item> implements Iterable<Item> {
    private Node first, last;

    private class Node{
        Item item;
        Node next;
        Node prev;
    }

    private int N;

    // construct an empty deque
    public Deque(){
        N = 0;
    }

    // is the deque empty?
    public boolean isEmpty() {
        return  (N == 0);
    }

    // return the number of items on the deque
    public int size() {
        return N;
    }

    // add the item to the front
    public void addFirst(Item item) {
        if (item == null) {
            throw new java.lang.NullPointerException("New item is a null.");
        }
        if (isEmpty()) {
            first = new Node();
            last = first;
            first.item = item;
        } else {
            Node oldfirst = first;
            first = new Node();
            first.item = item;
            first.next = oldfirst;
            first.next.prev = first;
        }
        N++;
    }

    // add the item to the end
    public void addLast(Item item) {
        if (item == null) {
            throw new java.lang.NullPointerException("New item is a null.");
        }
        if (isEmpty()) {
            first = new Node();
            last = first;
            last.item = item;
        } else {
            Node oldlast = last;
            last = new Node();
            last.item = item;
            last.prev = oldlast;
            last.prev.next = last;
        }
        N++;
    }

    // remove and return the item from the front
    public Item removeFirst() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        Item removedItem = first.item;
        first = first.next;
        if(size() != 1) {
            first.prev = null;
        }
        N--;
        if (isEmpty()) {
            last = null;
        }
        return removedItem;
    }

    // remove and return the item from the end
    public Item removeLast() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        Item removedItem = last.item;
        last = last.prev;
        if(size() != 1) {
            last.next = null;
        }
        N--;
        if (isEmpty()) {
            first = null;
        }
        return removedItem;
    }

    // return an iterator over items in order from front to end
    public Iterator<Item> iterator() {
        return new DoublyListIterator();
    }

    private class DoublyListIterator implements Iterator<Item>{
        private Node curr = first;

        @Override
        public void remove() {
            throw new java.lang.UnsupportedOperationException("Why do you" +
                    "use it?");
        }

        @Override
        public boolean hasNext() {
            return curr != null;
        }

        @Override
        public Item next() {
            if (!hasNext()) {
                throw new java.util.NoSuchElementException("There are no" +
                        " more items to return.");
            }
            Item item = curr.item;
            curr = curr.next;
            return item;
        }
    }

    // unit testing
    public static void main(String[] args) {
        Deque<String> dq = new Deque<>();
        while (!StdIn.isEmpty())
        {
            String s = StdIn.readString();
            if (s.equals("0")) break;
            else if(s.equals("-")) StdOut.print(dq.removeFirst());
            else dq.addFirst(s);
        }
        dq.addFirst("1");
        dq.addFirst("2");
        dq.addLast("3");
        dq.removeFirst();
        dq.removeLast();
        dq.removeFirst();

        for (String s: dq) {
            System.out.print(s + " ");
        }
    }
}
