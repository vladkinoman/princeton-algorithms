import java.util.NoSuchElementException;
import edu.princeton.cs.algs4.Stack;
import java.util.Scanner;
import java.lang.System;

public class Buffer
{
	private int N;
	private Stack<Character> leftStack;
	private Stack<Character> rightStack; 

	public Buffer() {
		leftStack = new Stack<Character>();
		rightStack = new Stack<Character>();
		N = 0;
	}

	public void insert(char c) { // works like standard insert
		leftStack.push(c);
		N++;
	} 

	public char delete() { // works like backspace 
		if(leftStack.isEmpty())
			throw new NoSuchElementException();
		char c = leftStack.pop();
		N--;
		return c;
	}

	public void left(int k) {
		for (int i = 0; i < k ;i++) {
			if(!leftStack.isEmpty())
				rightStack.push(leftStack.pop());
			else break;
		}
	}

	public void right(int k) {
		for (int i = 0; i < k ;i++) {
			if(!rightStack.isEmpty())
				leftStack.push(rightStack.pop());
			else break;
		}
	}

	public int size(){
		return N;
	}

	/*example:
	input: abcde<2-hx>4-<1-
	output:c e x 
	*/
	public static void main(String[] args) {
		Scanner scanner = new Scanner(System.in);
		Buffer buffer = new Buffer();
		
		while(scanner.hasNext())
		{
			String item = scanner.next();
			for (int i = 0; i < item.length(); i++) {
				char c = item.charAt(i);
				if(c == '-')
					System.out.print(buffer.delete() + " ");
				else if(c == '>')
				{
					if((i + 1) < item.length())
					{
						i++;
						buffer.right(Integer.parseInt(Character.toString(item.charAt(i))));
					}
					else buffer.insert(c);
				}
				else if(c == '<')
				{
					if((i + 1) < item.length())
					{
						i++;
						buffer.left(Integer.parseInt(Character.toString(item.charAt(i))));
					}
					else buffer.insert(c);
				}
				else buffer.insert(c);
			}
		}
		System.out.println("size = " + buffer.size());
	}
}