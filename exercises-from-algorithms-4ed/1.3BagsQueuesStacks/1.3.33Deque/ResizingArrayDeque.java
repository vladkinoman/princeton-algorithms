

public class ResizingArrayDeque<Item> implements Iterable<Item>
{
	private Item deque[];
	private int first;
	private int last;
	private int N;

	public Deque()
	{
		first = 0;
		last = 0;
		N = 0;
		deque = (Item []) new Object[2];
	}

	public boolean isEmpty(){return N == 0;}

	public int size(){ return N;}

	private void resize(int size)
	{
		Item[] tmp = (Item[]) new Object[size];
		for (int i = 0; i < deque.length; i++) {
			tmp[i] = deque[(first + i) % deque.length];
		}
		deque = tmp;
		first = 0;
		last = N;
	}
	
	public void pushLeft(Item item)
	{
		if(N == deque.length) resize(2 * deque.length);
		deque[--first] = item;
		if(first)
		N++;
	}

	public void pushRight(Item item)
	{
		if(N == deque.length) resize(2 * deque.length);
		deque[last++] = item;
		//if(last == deque.length) last = 0;
		N++;
	}

	public Item popLeft()
	{

	}

	public Item popRight()
	{

	}

	public Iterator<Item> iterator()
	{
		return new ResizingArrayIterator();
	}

	private class ResizingArrayIterator implements Iterator<Item>
	{
		private int current = first;

		public boolean hasNext()
		{

		}

		public Item next()
		{

		}

		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		
	}
}