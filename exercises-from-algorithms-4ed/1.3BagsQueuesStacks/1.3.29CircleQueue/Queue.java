import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import java.util.Iterator;

public class Queue<Item> implements Iterable<Item>
{
	private Node last;
	private int N;

	private class Node
	{
		Node next;
		Item item;
	}

	public void enqueue(Item item)
	{
		if(N!=0) 
		{
			Node tmp = last.next; // ref on head
			last.next = new Node();
			last.next.item = item;
			last = last.next;
			last.next = tmp;
		}
		else
		{
			last = new Node();
			last.item = item;
			last.next = last;
		}
		N++;
	}

	public Item dequeue()
	{
		Item tmp = null;
		if(N != 0)
		{
			tmp = last.next.item;
			if(N != 1) last.next = last.next.next;
			else       last = null;
			N--;
		}
		else
			System.out.println("You can't dequeue. Queue is empty :(");
		
		return tmp;
	}

	public boolean isEmpty()
	{
		return N == 0;
	}

	public int size()
	{
		return N;
	}

	public Iterator<Item> iterator()
	{
		return new CircularLinkedListIterator();
	}

	private class CircularLinkedListIterator implements Iterator<Item>
	{
		private Node current;
		private boolean isHeadNotProcessed = true;

		public CircularLinkedListIterator()
		{
			if(last != null) current = last.next;
			else throw new NullPointerException("List is empty.");
		}
		
		public Item next()
		{
			Item item = current.item;
			if(current == last.next) isHeadNotProcessed = false;
			current = current.next;
			return item;
		}
		
		public boolean hasNext()
		{
			return isHeadNotProcessed || current != last.next ;
		}
		
		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		Queue<String> queue = new Queue<String>();
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