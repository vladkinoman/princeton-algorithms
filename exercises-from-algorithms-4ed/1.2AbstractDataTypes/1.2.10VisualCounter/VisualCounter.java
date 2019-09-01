import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdDraw;

public class VisualCounter
{
	private int operationCount;
	private final int N; 		// number of operations
	private final int max;      // maximum absolute value for the counter
	private int count; 	// current value

	VisualCounter(int N, int max)
	{
		this.N = N;
		this.max = max;
		StdDraw.setPenColor(StdDraw.BOOK_RED);
		StdDraw.setPenRadius(.01);
		StdDraw.setXscale(0, N);
		StdDraw.setYscale(0, max);
	}

	public void increment()
	{
		if(count < max && operationCount < N)
		{
			count++;
			operationCount++;
			StdDraw.point(operationCount, count);
		}
		else
			StdOut.printf("You can't increment anymore!\n");
	}

	public void decrement()
	{
		if(count > 0 && operationCount < N)
		{
			count--;
			operationCount++;
			StdDraw.point(operationCount, count);
		}
		else
			StdOut.printf("You can't decrement anymore!\n");
	}

	public int tally()
	{
		return count;
	}

	public String toString()
	{
		return "count = " + count;
	}

	public static void main(String[] args) {
		int N = Integer.parseInt(args[0]);
		int max = Integer.parseInt(args[1]);
		VisualCounter count = new VisualCounter(N, max);
		while(!StdIn.isEmpty())
		{
			String readS = StdIn.readString();
			if(readS.equals("+"))
				count.increment();
			else if(readS.equals("-"))
				count.decrement();
		}
		StdOut.printf("%s\n", count);
	}
}