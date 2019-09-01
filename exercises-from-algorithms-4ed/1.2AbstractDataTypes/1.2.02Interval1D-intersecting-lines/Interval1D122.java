import edu.princeton.cs.algs4.Interval1D;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

public class Interval1D122
{
	public static void main(String[] args) {
		int N = Integer.parseInt(args[0]);
		Interval1D [] intervalArr = new Interval1D[N];
		for (int i = 0; i < N && !StdIn.isEmpty(); i++) {
			double min = StdIn.readDouble();
			double max = StdIn.readDouble();
			intervalArr[i] = new Interval1D(min, max);
		}

		for (int i = 0; i < N - 1; i++)
			for (int j = i + 1; j < N; j++)
				if(intervalArr[i].intersects(intervalArr[j]))
					StdOut.printf("Intervals %s and %s intersect.\n",
						intervalArr[i], intervalArr[j]);
	}
}