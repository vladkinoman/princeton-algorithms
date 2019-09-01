import java.util.Iterator;
import java.util.Scanner;
import java.util.Random;
import java.lang.System;
import java.util.NoSuchElementException;

public class RandomQueue<Item> implements Iterable<Item>
{
	private Item queue[];
	private int N;
	private Random random;

	public RandomQueue()
	{
		queue = (Item[]) new Object[2];
		N = 0;
		random = new Random(System.currentTimeMillis());
	}

	public int size()
	{
		return N;
	}

	public boolean isEmpty()
	{
		return N == 0;
	}

	public void enqueue(Item item)
	{
		if(N == queue.length) resize(2 * queue.length);
		queue[N++] = item;
	}

	public Item dequeue()
	{
		if (isEmpty()) throw new NoSuchElementException("Deque underflow");
		int ri = random.nextInt(N);
		Item item = queue[ri];
		queue[ri] = queue[--N];
		queue[N] = null; // without replacement
		if(N > 0 && N == queue.length / 4) resize(queue.length / 2);
		return item;
	}

	public Item sample()
	{
		if (isEmpty()) throw new NoSuchElementException("Deque underflow");
		int ri = random.nextInt(queue.length);
		Item item = queue[ri];
		queue[ri] = queue[--N];
		queue[N++] = item; // with replacement
		return item;
	}

	public Iterator<Item> iterator()
	{
		return new ResizingArrayIterator();
	}

	private void resize(int newSize)
	{
		Item tmp [] = (Item []) new Object[newSize];
		for (int i = 0;i < N;i++)
			tmp[i] = queue[i];
		queue = tmp;
	}

	private class ResizingArrayIterator implements Iterator<Item>
	{
		private int current = 0;

		public boolean hasNext()
		{
			return current != N;
		}

		public Item next()
		{
			return queue[current++];
		}	

		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		Scanner scanner = new Scanner(System.in);
		RandomQueue<String> rqueue = new RandomQueue<String>();
		while(scanner.hasNext())
		{
			String item = scanner.next();
			if(!item.equals("-")) rqueue.enqueue(item);
			else if(!item.isEmpty()) System.out.print(rqueue.dequeue() + " ");
		}
		for (String item : rqueue) {
			System.out.print(item + " ");
		}
		System.out.println();
	}
}