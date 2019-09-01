import java.util.Iterator;
import java.util.ConcurrentModificationException;
import java.util.NoSuchElementException;
import java.util.Scanner;

public class Stack<Item> implements Iterable<Item>
{
	private Node first;
	private int N;
	private int operationCounter;
	private class Node {
		Node next;
		Item item;
	}

	public int size(){
		return N;
	}

	public boolean isEmpty(){
		return N == 0;
	}

	public void push(Item item) {
		operationCounter++;
		Node oldFirst = first;
		first = new Node();
		first.item = item;
		first.next = oldFirst;
		N++;
	}

	public Item pop(){
		operationCounter++;
		if(N == 0) throw new NoSuchElementException("Underflow!");
		Item item = first.item;
		first = first.next;
		--N;
		return item;
	}

	public Iterator<Item> iterator(){
		return new LinkedListIterator();
	}

	private class LinkedListIterator implements Iterator<Item>
	{
		private Node current = first;
		private int currentOperationCounter = operationCounter;

		public boolean hasNext()
		{
			if(currentOperationCounter != operationCounter)
				throw new ConcurrentModificationException();
			return current != null;
		}

		public Item next()
		{
			if(currentOperationCounter != operationCounter)
				throw new ConcurrentModificationException();
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
		Stack<String> stack = new Stack<String>();
		Scanner scanner = new Scanner(System.in);
		while(scanner.hasNext())
		{
			String item = scanner.next();
			if(!item.equals("-")) stack.push(item);
			else if(!item.isEmpty()) 
				System.out.print(stack.pop() + " ");			
		}

		for (String item : stack) {
			stack.push(item);
			System.out.print(item + " ");
			stack.pop();
		}
		System.out.println();
	}
}