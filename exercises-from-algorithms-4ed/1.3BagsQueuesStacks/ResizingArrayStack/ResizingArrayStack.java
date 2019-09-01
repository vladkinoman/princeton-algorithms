import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

import java.util.Iterator;

public class ResizingArrayStack<Item> implements Iterable<Item>
{
	private int N = 0; // stack pointer
	private Item a [] = (Item []) new Object [1];

	public void push(Item item)
	{
		if(N == a.length) resize(2 * a.length);
		a[N++] = item; 
	}

	public Item pop()
	{
		Item tmp = a[--N];
		a[N] = null; // to avoid loitering
		if(N > 0 && N == a.length / 4) resize(a.length / 2);
		return tmp;
	}

	public int size()
	{
		return N;
	}

	public boolean isEmpty()
	{
		return N == 0;
	}

	private void resize(int size)
	{
		Item tmp [] = (Item []) new Object [size];
		for (int i = 0; i < N; i++)
			tmp[i] = a[i];
		a = tmp;
	}

	public Iterator<Item> iterator()
	{
		return new ReverseArrayIterator();
	}

	private class ReverseArrayIterator implements Iterator<Item>
	{
		int i = N;

		public boolean hasNext()
		{
			return i > 0;
		}

		public Item next()
		{
			return a[--i];
		}

		public void remove(){throw new UnsupportedOperationException();}
	} 

	public static void main(String[] args) {
		ResizingArrayStack<String> stack = new ResizingArrayStack<String>();
		while(!StdIn.isEmpty())
		{
			String item = StdIn.readString();
			if(!item.equals("-"))
				stack.push(item);
			else if(!stack.isEmpty()) StdOut.print(stack.pop() + " ");
		}
		StdOut.println("There are " + stack.size() + " left in stack.");
		for (String s : stack) {
			StdOut.print(s + " ");
		}
		StdOut.println();
	}
}