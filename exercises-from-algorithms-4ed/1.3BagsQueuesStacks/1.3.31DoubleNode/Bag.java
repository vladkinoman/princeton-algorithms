import java.util.Iterator;

public class Bag<Item> implements Iterable<Item>
{
	private DoubleNode first;
	private int N;
	private class DoubleNode
	{
		DoubleNode prev;
		DoubleNode next;
		Item item;
	}

	public void addAtBeggining(Item item)
	{
		Node oldFirst = first;
		first = new DoubleNode();
		first.item = item;
		first.next = oldFirst;
		N++;
	}

	public void addAtEnd(Item item)
	{
		Node oldlast;
		for (oldlast = first; oldlast.next != null; oldlast = oldlast.next)
			;
		oldlast.next = new Node();
		oldlast.next.item = item;
		N++;
	}

	public Iterator<Item> iterator()
	{
		return new LinkedListIterator();
	}

	private class LinkedListIterator implements Iterator<Item>
	{
		DoubleNode current = first;

		public boolean hasNext()
		{
			return current != null;
		}

		public Item next()
		{
			Item item = current.item;
			current = current.item;
			return item;
		}

		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		
	}
}