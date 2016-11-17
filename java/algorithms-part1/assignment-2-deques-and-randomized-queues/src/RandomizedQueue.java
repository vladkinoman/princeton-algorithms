import java.util.Iterator;

import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdRandom;

public class RandomizedQueue<Item> implements Iterable<Item> {
    private Item[] s;
    private int N;
    private int tail;

    // construct an empty randomized queue
    public RandomizedQueue() {
        N = tail = 0;
        s = (Item[]) new Object[N+1];
    }

    // is the queue empty?
    public boolean isEmpty() {
        return N == 0;
    }

    // return the number of items on the queue
    public int size() {
        return N;
    }

    // add the item (to the tail of queue)
    public void enqueue(Item item) {
        if (item == null) {
            throw new java.lang.NullPointerException("New item is a null.");
        }
        if (N == s.length) resize(2 * s.length);
        s[tail++] = item;
        N++;
    }

    // remove and return a random item
    public Item dequeue() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        int randPos = StdRandom.uniform(0, N);
        Item item = s[randPos];
        s[randPos] = null;
        if (N > 0 && N == s.length / 4) resize(s.length / 2);
        N--;
        return item;
    }

    // return (but do not remove) a random item
    public Item sample() {
        if (isEmpty()) {
            throw new java.util.NoSuchElementException("Deque is empty.");
        }
        int randPos = StdRandom.uniform(0, N);
        return s[randPos];
    }

    // return an independent iterator over items in random order
    @Override
    public Iterator<Item> iterator() {
        return new RandomizedQueueIterator<Item>();
    }

    // resize an array to fixed capacity
    private void resize(int capacity) {
        Item[] newArray = (Item[]) new Object[capacity];
        for (int i = 0; i < N; i++) {
            newArray[i] = s[i];
        }
        s = newArray;
    }

    private class RandomizedQueueIterator<Item> implements Iterator<Item> {
        private Item[] randomizedQueue;
        private int next;

        private RandomizedQueueIterator() {
            randomizedQueue = (Item[]) new Object[s.length];
            for (int i = 0; i < s.length; i++) {
                randomizedQueue[i] = (Item) s[i];
            }
            StdRandom.shuffle(randomizedQueue);
            next = 0;
        }

        @Override
        public boolean hasNext() {
            return next < randomizedQueue.length;
        }

        @Override
        public Item next() {
            if (!hasNext()) {
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
