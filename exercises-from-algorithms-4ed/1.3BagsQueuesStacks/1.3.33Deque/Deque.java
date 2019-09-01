import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Scanner;
import java.lang.System;// they use java.io.PrintWriter
import java.util.Locale;

public class Deque<Item> implements Iterable<Item>
{
	private Node first;
	private Node last;
	private int N;

	private class Node
	{
		Node next;
		Node prev;
		Item item;
	}

	public Deque()
	{

	}

	public boolean isEmpty()
	{
		return N == 0;
	}

	public int size()
	{
		return N;
	}

	public void pushLeft(Item item)
	{
		Node oldfirst = first;
		first = new Node();
		first.next = oldfirst;
		first.prev = null;
		first.item = item;
		if(isEmpty()) last = first;
		else oldfirst.prev = first;
		N++;
	}

	public void pushRight(Item item)
	{
		Node oldlast = last;
		last = new Node();
		last.item = item;
		last.next = null;
		last.prev = oldlast;
		if(isEmpty()) first = last;
		else oldlast.next = last;
		N++;
	}

	public Item popLeft()
	{
		if (isEmpty()) throw new NoSuchElementException("Deque underflow");
		Item item = first.item;
		first = first.next;
		N--;
		if(isEmpty()) last = first;
		else first.prev = null; 
		return item;
	}

	public Item popRight()
	{
		if (isEmpty()) throw new NoSuchElementException("Deque underflow");
		Item item = last.item;
		last = last.prev;
		N--;
		if(isEmpty()) first = last;
		else last.next = null; 
		return item;
	}
	
	public Iterator<Item> iterator()
	{
		return new LinkedListIterator();
	}

	private class LinkedListIterator implements Iterator<Item>
	{
		private Node current = first;

		public boolean hasNext()
		{
			return current != null;
		}

		public Item next()
		{
			Item item = current.item;
			current = current.next;
			return item;
		}

		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		Deque<String> dq = new Deque<String>();
		Scanner scanner = new Scanner(System.in);
		while(scanner.hasNext())
		{
			String action = scanner.next();
			if     (action.equals("+left"))
			{
				String item = scanner.next();
				dq.pushLeft(item);
			}
			else if(action.equals("+right"))
			{
				String item = scanner.next();
				dq.pushRight(item);
			}
			else if(action.equals("-left"))
			{
				System.out.println(dq.popLeft() + " ");
			}
			else if(action.equals("-right"))
			{
				System.out.println(dq.popRight() + " ");
			}
		}

		System.out.println("Here is the deque:");
		for (String s: dq) {
			System.out.print(s + " ");	
		}
		System.out.println();
	}
}