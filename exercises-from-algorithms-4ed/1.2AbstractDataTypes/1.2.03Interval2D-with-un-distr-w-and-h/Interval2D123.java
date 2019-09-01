import edu.princeton.cs.algs4.Interval1D;
import edu.princeton.cs.algs4.Interval2D;
import edu.princeton.cs.algs4.StdRandom;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

public class Interval2D123
{
	public static void main(String[] args) {
		int N = Integer.parseInt(args[0]);
		double min = Double.parseDouble(args[1]);
		double max = Double.parseDouble(args[2]);
		Interval2D[] boxArray = new Interval2D[N];
		double[][] points = new double[N][4];
		for (int i = 0; i < N ; i++ ) {
			points[i] = new double[4];
		}
		for (int i = 0;  i < N ; i++ ) {
			double xlo = StdRandom.uniform(min, max);
			double xhi = StdRandom.uniform(min, max);
			if (xlo > xhi)
			{
				double tmp = xlo;
				xlo = xhi;
				xhi = tmp;
			}

			double ylo = StdRandom.uniform(min, max);
			double yhi = StdRandom.uniform(min, max);
			if (ylo > yhi)
			{
				double tmp = ylo;
				ylo = yhi;
				yhi = tmp;
			}

			Interval1D xint = new Interval1D(xlo, xhi);
			Interval1D yint = new Interval1D(ylo, yhi);
			boxArray[i] = new Interval2D(xint, yint);
			boxArray[i].draw();
			points[i][0] = xlo;
			points[i][1] = xhi;
			points[i][2] = ylo;
			points[i][3] = yhi;
		}
		
		int numberOfIntersectedPairsOfIntervals = 0;
		int numberOfIntervalsThatAreContainedInOneAnother = 0;
		for (int i = 0; i < N - 1; i++) {
			for (int j = i+1; j < N ;j++) {
				if(boxArray[i].intersects(boxArray[j])) // if order isn't important
					numberOfIntersectedPairsOfIntervals++;
				// we count "container" twice if there are two extern squares that contain it! 
				if(points[j][0] <= points[i][0] 
					&& points[j][1] >= points[i][1]
					&& points[j][2] <= points[i][2]
					&& points[j][3] >= points[i][3])
					numberOfIntervalsThatAreContainedInOneAnother++;
				else if(points[j][0] >= points[i][0]
					&& points[j][1] <= points[i][1]
					&& points[j][2] >= points[i][2]
					&& points[j][3] <= points[i][3])
					numberOfIntervalsThatAreContainedInOneAnother++;

			}
		}
		StdOut.printf("# of intersected pairs = %d\n",numberOfIntersectedPairsOfIntervals);
		StdOut.printf("# of intervals that are contained in one another = %d\n",
			numberOfIntervalsThatAreContainedInOneAnother);
	}
}