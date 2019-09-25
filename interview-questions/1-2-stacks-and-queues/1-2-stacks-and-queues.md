# Interview Questions: Stacks and Queues

## Queue with two stacks

**Question**. Implement a queue with two stacks so that each queue operations takes a constant amortized number of stack operations.﻿

**Answer**. Solution:

```Java
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
}
```

> *Hint*: If you push elements onto a stack and then pop them all, they appear in reverse order. If you repeat this process, they're now back in order.

## **Stack with max**

**Question**. Create a data structure that efficiently supports the stack operations (push and pop) and also a return-the-maximum operation. Assume the elements are real numbers so that you can compare them.

**Answer**. Short solution:

```Java
import java.util.NoSuchElementException;
// based on linked list version of Stack
public class StackWithMax {
    // class's data as before
	private int max = Integer.MIN_VALUE;
    
    public void push(int elem) {
        if (max < elem) 
            max = elem;
        // as before
    }
    
    // not as effective as we need :(
    public int pop() {
        // as before
        if (elem == max)
        {
            int prevMax = max;
            max = Integer.MIN_VALUE;
            for (Node curr = first; curr != NULL; curr=curr.next)
                if (curr.info != prevMax && curr.info > max)
                    max = curr.info;
        }
        return elem;
    }
    
    public int returnMax() {
        if (size() == 0)
            throw new NoSuchElementException();
        return max;
    }
}
```

That was an unexpected hint :) TODO: try this approach later.

> *Hint*: Use two stacks, one to store all of the items and a second stack to store the maximums.

## Java generics

**Question**. Explain why Java prohibits generic array creation.

**Answer**. The main problems with java generics is that arrays in Java are covariant, but generics are not. In other words, `Integer[]` is a subtype of `Object[]`, but `Stack<Integer>` is not a subtype of `Stack<Object>`.

> *Hint*: to start, you need to understand that Java arrays are covariant but Java generics are not: that is, String[] is a subtype of Object[], but Stack<String> is not a subtype of Stack<Object>.