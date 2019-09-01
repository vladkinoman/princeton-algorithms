import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import java.util.Iterator;

public class ResizingArrayQueue<Item> implements Iterable<Item>
{
	private int head;
	private int tail;
	private int N;
	private Item q[];

	public ResizingArrayQueue()
	{
		head = 0;
		tail = 0;
		N = 0;
		q = (Item []) new Object[2];
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
		if(N == q.length) resize(q.length * 2);
		q[tail++] = item;
		if(tail == q.length) tail = 0;
		N++;
	}

	public Item dequeue()
	{
		if (isEmpty()) throw new NoSuchElementException("Queue underflow");
		
		Item tmp = q[head];
		q[head++] = null;
		N--;
		
		if(head == q.length) head = 0; //wrap-around
		// shrink size of array if necessary
		if(N > 0 && N == (q.length / 4)) resize(q.length / 2);
		return tmp;
	}

	private void resize(int max)
	{
		Item tmp[] = (Item []) new Object[max];
		for (int i = 0; i < q.length ;i++ )
			tmp[i] = q[(head + i) % q.length];
		q = tmp;
		tail = N;
		head = 0;
	}

	public Iterator<Item> iterator()
	{
		return new ArrayIterator();
	}

	private class ArrayIterator implements Iterator<Item>
	{
		int i = head;

		public boolean hasNext()
		{
			return i < tail;
		}

		public Item next()
		{
			return q[i++];
		}

		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		ResizingArrayQueue<String> queue = new ResizingArrayQueue<String>();
		while(!StdIn.isEmpty())
		{
			String s = StdIn.readString();
			if     (!s.equals("-")) queue.enqueue(s);
			else if(!s.isEmpty())  StdOut.println(queue.dequeue());
		}

		StdOut.println("Here is the queue:");
		for (String s: queue) {
			StdOut.print(s + " ");	
		}
		StdOut.println();
	}
}