import java.util.Iterator;

import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdRandom;

public class RandomizedQueue<Item> implements Iterable<Item> {
    private Item[] s;
    private int tail;

    // construct an empty randomized queue
    public RandomizedQueue() {
        tail = 0;
        s = (Item[]) new Object[tail + 1];
    }

    // is the queue empty?
    public boolean isEmpty() {
        return tail == 0;
    }

    // return the number of items on the queue
    public int size() {
        return tail;
    }

    // add the item (to the tail of queue)
    public void enqueue(Item item) {
        if (item == null) {
            throw new java.lang.NullPointerException("New item is a null.");
        }
        if (tail == s.length) resize(2 * s.length);
        s[tail++] = item;
    }

    // remove and return a random item
    public Item dequeue() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        int randPos = StdRandom.uniform(0, tail);
        Item item = s[randPos];
        s[randPos] = null;
        if (randPos < tail - 1) {
            /***************** bias *****************/
            for (int i = randPos; i < tail; i++) {
                s[i] = s[i + 1];
            }
        }
        tail = tail - 1;
        if (tail > 0 && tail == s.length / 4) resize(s.length / 2);
        return item;
    }

    // return (but do not remove) a random item
    public Item sample() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        int randPos = StdRandom.uniform(0, tail);
        return s[randPos];
    }

    // resize an array to fixed capacity
    private void resize(int capacity) {
        Item[] newArray = (Item[]) new Object[capacity];
        for (int i = 0; i < tail; i++) {
            newArray[i] = s[i];
        }
        s = newArray;
    }

    // return an independent iterator over items in random order
    @Override
    public Iterator<Item> iterator() {
        return new RandomizedQueueIterator<Item>();
    }

    private class RandomizedQueueIterator<Item> implements Iterator<Item> {
        private Item[] randomizedQueue;
        private int next;

        private RandomizedQueueIterator() {
            Item[] aux = (Item []) new Object[s.length];
            aux = (Item[]) s.clone();
            StdRandom.shuffle(aux);
            randomizedQueue = (Item[]) new Object[s.length];
            for (int i = 0, j = 0; i < aux.length; i++) {
                if (aux[i] != null) {
                    randomizedQueue[j] = aux[i];
                    j++;
                }
            }
            next = 0;
        }

        @Override
        public boolean hasNext() {
            return randomizedQueue[next] != null;
        }

        @Override
        public Item next() {
            if (next == randomizedQueue.length) {
                throw new java.util.NoSuchElementException("There are no" +
                        " more items to return.");
            }
            return randomizedQueue[next++];
        }

        @Override
        public void remove() {
            throw new java.lang.UnsupportedOperationException("Why do you" +
                    "use it?");
        }
    }
    // unit testing
    public static void main(String[] args) {
        RandomizedQueue<String> rq = new RandomizedQueue<>();
        while (!StdIn.isEmpty())
        {
            String s = StdIn.readString();
            if (s.equals("0")) break;
            else if(s.equals("-")) StdOut.print(rq.dequeue());
            else rq.enqueue(s);
        }

        for (String s: rq) {
            System.out.print(s + " ");
        }
        Iterator<String> it1 = rq.iterator();
        Iterator<String> it2 = rq.iterator();
    }
}
