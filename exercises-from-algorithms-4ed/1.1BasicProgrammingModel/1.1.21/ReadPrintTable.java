import edu.princeton.cs.algs4.*;

public class ReadPrintTable
{
	public static void main(String[] args) {
		StdOut.printf("%20s %3s %3s %4s \n", "Name", "i", "j", "result");
		while(!StdIn.isEmpty())
		{
			String name = StdIn.readString();
			int i = StdIn.readInt();
			int j = StdIn.readInt();
			StdOut.printf("%20s  %d  %d  %.3f\n", name, i, j, (i*1.0) / j);
		}
	}
}