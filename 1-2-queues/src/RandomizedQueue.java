
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdRandom;
import java.util.Iterator;
import java.util.NoSuchElementException;
// also you can use java.lang

/**
 The {@code RandomizedQueue} class represents a randomized queue of generic items.
 *  It supports adding and removing items uniformly at random,
 *  and iterating over the items in uniformly random order.
 *  The order of two or more iterators to the same randomized queue is mutually independent;
 *  each iterator maintains its own random order.
 *  <p>
 *  This implementation uses a ... with a ... .
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 *
 * @param <Item> the generic type of an item in this randomized queue
 */
public class RandomizedQueue<Item> implements Iterable<Item> {

    private Item[] resizingArray;
    private int head;
    private int tail;
    private int count;
    /**
     * Constructs an empty randomized queue.
     */
    public RandomizedQueue() {
        resizingArray = (Item[]) new Object[1];
        head = 0;
        tail = 0;
        count = 0;
    }

    /**
     * Returns true if the queue is empty.
     *
     * @return {@code true} if the queue is empty;
     *         {@code false} otherwise
     */
    public boolean isEmpty() {
        return count == 0;
    }

    /**
     * Returns the number of items on the queue.
     *
     * @return the number of items on the queue
     */
    public int size() {
        return count;
    }

    /**
     * Adds the item to the queue.
     *
     * @param item the item which is added to the queue
     * @throws IllegalArgumentException if the client calls enqueue() with a null argument
     */
    public void enqueue(Item item) {
        if (item == null) throw new IllegalArgumentException();
        if (count == resizingArray.length || tail == resizingArray.length)
            resize(2 * resizingArray.length);
        resizingArray[tail++] = item;
        count++;
    }

    private void resize(int capacity) {
        Item[] copy = (Item[]) new Object[capacity];

        int i = 0;
        for (int j = 0; i < count; j++) {
            if (resizingArray[j] != null) {
                copy[i] = resizingArray[j];
                i++;
            }
        }

        resizingArray = copy;
        head = 0;
        tail = count;
    }

    /**
     * Removes and returns a random item.
     *
     * @return a random item removing it
     * @throws NoSuchElementException if the client calls dequeue() when the randomized queue is empty
     */
    public Item dequeue() {
        if (isEmpty()) throw new NoSuchElementException();
        int randomPlace = 0;
        Item item = null;
        do {
            randomPlace = StdRandom.uniform(head, tail);
        } while ((item = resizingArray[randomPlace]) == null);
        resizingArray[randomPlace] = null;
        count--;
        if (count > 0) {
            // invariant: array is between 25% and 100% full.
            if (count == resizingArray.length / 4) {
                resize(resizingArray.length / 2);
            } else if (head == randomPlace) {
                // invariant: head is in the interval [0; tail)
                // && array[head] == null
                for (; resizingArray[head] == null; head++)
                    ;
            } else if (tail == randomPlace - 1) {
                // invariant: tail is in the interval (head; length of the array]
                // && array[tail - 1] == null && array[head] != null
                for (; resizingArray[tail - 1] == null; --tail)
                    ;
            }
        } else if (count == 0) {
            head = 0;
            tail = 0;
        }
        return item;
    }

    /**
     * Returns a random item (but doesn't remove it).
     *
     * @return a random item without removing it
     * @throws NoSuchElementException if the client calls sample() when the randomized queue is empty
     */
    public Item sample() {
        if (isEmpty()) throw new NoSuchElementException();
        int randomPlace = 0;
        Item item = null;
        do {
            randomPlace = StdRandom.uniform(head, tail);
        } while ((item = resizingArray[randomPlace]) == null);
        return item;
    }

    /**
     * Return an independent iterator over items in random order
     *
     * @return an iterator that iterates over the items in random order
     */
    public Iterator<Item> iterator() {
        return new RandomizedQueueIterator();
    }

    private class RandomizedQueueIterator implements Iterator<Item> {

        private final Item[] currentArray;
        private int curr;

        /**
         * Construct iterator for randomized queue.
         */
        RandomizedQueueIterator() {
            currentArray = (Item[]) new Object[count];

            int i = 0;
            for (int j = 0; i < count; j++) {
                if (resizingArray[j] != null) {
                    currentArray[i] = resizingArray[j];
                    i++;
                }
            }

            StdRandom.shuffle(currentArray);
            curr = 0;
        }

        @Override
        public boolean hasNext() {
            return curr != currentArray.length;
        }

        @Override
        public Item next() {
            if (!hasNext()) throw new NoSuchElementException();
            return currentArray[curr++];
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Unit tests the {@code RandomizedQueue} data type. (required)
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        RandomizedQueue<String> randqueue = new RandomizedQueue<>();
        while (!StdIn.isEmpty()) {
            String sign = StdIn.readString();
            switch (sign) {
                case "+":
                    String item = StdIn.readString();
                    randqueue.enqueue(item);
                    break;
                case "-s":
                    if (!randqueue.isEmpty())
                        StdOut.print(randqueue.sample() + " ");
                    break;
                case "-d":
                    if (!randqueue.isEmpty())
                        StdOut.print(randqueue.dequeue() + " ");
                    break;
                default:
                    break;
            }
        }
        StdOut.println("(" + randqueue.size() + " left on rand queue)");
        for (String str : randqueue) {
            StdOut.print(str + " ");
        }
    }

}
