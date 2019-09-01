
import java.util.Iterator;
import java.util.Random;
import java.util.Scanner;
import java.lang.System;

public class RandomBag<Item> implements Iterable<Item>
{
	private Item bag[];
	private int last;
	private int N;

	public RandomBag()
	{
		bag = (Item[]) new Object[1];
		last = 0;
		N = 0;
	}
	public boolean isEmpty(){return N == 0;}
	public int size(){return N;}
	public Iterator<Item> iterator()
	{
		return new ResizingArrayIterator();
	}
	private void resize(int size)
	{
		Item[] tmp = (Item []) new Object[size];
		for (int i = 0; i < bag.length ;i++ ) {
			tmp[i] = bag[i];
		}
		bag = tmp;
	}
	public void add(Item item)
	{
		if(N == bag.length) resize(2 * bag.length);
		bag[last++] = item;
		N++;
	}
	private class ResizingArrayIterator implements Iterator<Item>
	{
		private Item randomBag[];
		private int current;

		public ResizingArrayIterator()
		{
			randomBag = (Item []) new Object[size()];
			for (int i = 0; i < size(); i++) {
				randomBag[i] = bag[i];
			}

			// shuffling
			Random random = new Random(System.currentTimeMillis());
			if (randomBag == null) {
            	throw new IllegalArgumentException("Array ref is null");
        	}
        	for (int i = 0; i < randomBag.length; i++) {
        		//uniformly distributed between i and n-1:
            	int r = i + random.nextInt(randomBag.length - i);
            	Object temp = randomBag[i];
            	randomBag[i] = randomBag[r];
           	 	randomBag[r] = (Item) temp;
        	}

        	current = last;
		}
		public boolean hasNext()
		{
			return current > 0;
		}
		public Item next()
		{
			Item item = randomBag[--current];
			return item;
		}
		public void remove()
		{
			throw new UnsupportedOperationException();
		}
	}

	public static void main(String[] args) {
		RandomBag<String> rbag = new RandomBag<String>();
		Scanner scanner = new Scanner(System.in);
		while(scanner.hasNext())
		{
			String item = scanner.next();
			rbag.add(item);
		}
		for (String item : rbag) {
			System.out.print(item + " ");
		}
		System.out.println();
	}
}