import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.StdRandom;
import edu.princeton.cs.algs4.StdOut;

public class Point2D121 
{
	public static void main(String[] args) {
		int N = Integer.parseInt(args[0]);
		Point2D [] parray = new Point2D[N];
		for (int i = 0; i < N ; i++) {
			Point2D p = new Point2D(StdRandom.uniform(),
				StdRandom.uniform());
			parray[i] = p;
			p.draw();
		}

		double distance = 0.0, tmp = 0.0;
		Point2D pa = null, pb = null;
		for (int i = 0; i < N - 1 ; i++, pa = null, pb = null, distance = 0.0) {
			for (int j = i + 1; j < N; j++) {
				if(i == (j - 1))
				{
					distance = parray[i].distanceTo(parray[j]);
					pa = parray[i];
					pb = parray[j];
				}
				else if ((tmp = parray[i].distanceTo(parray[j])) < distance)
				{
					distance = tmp;
					pa = parray[i];
					pb = parray[j];
				}
			}
			StdOut.printf("Distance btwn (%.3f, %.3f) and (%.3f, %.3f) = %f\n",
			 pa.x(), pa.y(), pb.x(), pb.y(), distance);
		}
	}
}