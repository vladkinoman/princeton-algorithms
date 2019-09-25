import edu.princeton.cs.algs4.Stack;
import java.util.NoSuchElementException;
import java.util.Iterator;

// Queue with two stacks:
// 1 stack is for pushing
// 2 stack is for poping
public class QueueWithTwoStacks<Item> implements Iterable<Item> {
	private Stack<Item> s1 = new Stack<Item>();
	private Stack<Item> s2 = new Stack<Item>();
	private int count = 0;

	public QueueWithTwoStacks() {

	}

	public boolean isEmpty() {
		return count == 0;
	}

	public int size() {
		return count;
	}

	public Item peek() {
		while(s1.size() != 0) {
			s2.push(s1.pop());
		}
		Item item = s2.peek();
		return item;
	}

	public void enqueue(Item item) {
		while(s2.size() > 0) {
			s1.push(s2.pop());
		}
		s1.push(item);
		count++;
	}

	public Item dequeue() {
		if (count == 0) {
			throw new NoSuchElementException("Underflow!");
		}

		while(s1.size() > 0) {
			s2.push(s1.pop());
		}
		Item item = s2.pop();
		count--;
		return item;
	}

	public Iterator<Item> iterator() {
		Iterator<Item> iterator;
		if  (s1.size() > 0)
			iterator = s1.iterator();
		else
			iterator = s2.iterator();
		return iterator;
	}

	// test client
	public static void main(String[] args) {
		QueueWithTwoStacks<String> qWithStacks = new QueueWithTwoStacks<String>();
		qWithStacks.enqueue("to");
		qWithStacks.enqueue("be");
		qWithStacks.enqueue("or");
		qWithStacks.enqueue("not");
		System.out.println(qWithStacks.dequeue());
		System.out.println(qWithStacks.dequeue());
		System.out.println("Printing................");
		qWithStacks.enqueue("not");
		for (String s : qWithStacks) {
			System.out.print(s + " ");
		}
		System.out.println();
	}
}
