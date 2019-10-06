import java.util.Arrays;

import edu.princeton.cs.algs4.StdDraw;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

public class BruteCollinearPoints {
    private final LineSegment[] segments;

    /**
     * Finds all line segments containing 4 points.
     * To check whether the 4 points p, q, r, and s are collinear,
     * we check whether the three slopes between p and q, between
     * p and r, and between p and s are all equal.
     *
     * @param inputPoints array which consists of objects of the Point dt
     */
    public BruteCollinearPoints(Point[] inputPoints) {
        // Checking corner cases...
        if (inputPoints == null)
            throw new IllegalArgumentException(
                    "Argument of the constructor is NULL.");

        for (Point p: inputPoints)
            if (p == null) throw new IllegalArgumentException(
                    "One of the points is NULL");

        for (int i = 0; i < inputPoints.length; i++)
            for (int j = i + 1; j < inputPoints.length; j++)
                if (inputPoints[j].compareTo(inputPoints[i]) == 0)
                    throw new IllegalArgumentException(
                            "Two points are equal.");

        Point[] points = new Point[inputPoints.length];
        for (int i = 0; i < inputPoints.length; i++) {
            points[i] = inputPoints[i];
        }

        // Sort points by natural order to make it easier
        // to find where p and s are in the next sequence: p->q->r->s.
        // Besides, sorting allows us not to miss the key points
        // in their iterative consideration (?).
        Arrays.sort(points);
        int n = points.length;
        // Create a large array to guarantee all collinear points will fit in
        Point[][] tmpPointSegments = new Point[n * n][];
        int countOfPointSegments = 0;
        // We are going through the all tuples of points
        for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
                for (int k = j + 1; k < n; k++) {
                    for (int m = k + 1; m < n; m++) {

                        if (Double.compare(points[i].slopeTo(points[j]),
                                points[i].slopeTo(points[k])) == 0
                        &&  Double.compare(points[i].slopeTo(points[j]),
                                points[i].slopeTo(points[m])) == 0) {
                            // We want to get only two points in the
                            //   segment p->q->r->s - p and s.
                            // I will choose the segment p->s (i->m).
                            // Sure, we can pick s->p segment if we want to.
                            tmpPointSegments[countOfPointSegments] =
                                    new Point[2];
                            tmpPointSegments[countOfPointSegments][0] =
                                    points[i];
                            tmpPointSegments[countOfPointSegments][1] =
                                    points[m];
                            countOfPointSegments++;

                        }
                    }
                }
            }
        }

        // Now, we want to remove subsegments.
        // In order to do that we should check slope between point (p1 or p2)
        // of the first segment and point (p1 or p2 - it doesn't matter)
        // of the next segment.
        LineSegment[] tmpLineSegments = new LineSegment[countOfPointSegments];
        int countOfLineSegments = 0;
        int j = 1;
        for (int i = 0; i < countOfPointSegments; i = j, j++) {

            // [i] points to the first slope.
            // [j] points to the next slopes.
            double firstSlope = tmpPointSegments[i][0]
                    .slopeTo(tmpPointSegments[i][1]);

            while (j < countOfPointSegments) {
                // We want to make sure that the segment being checked
                // enters the tmpPointSegments[i] segment.
                if ((Double.compare(tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][0]), firstSlope) != 0
                        && Double.compare(tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][0]),
                        Double.NEGATIVE_INFINITY) != 0)

                   || (Double.compare(tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][1]), firstSlope) != 0
                        && Double.compare(tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][1]),
                        Double.NEGATIVE_INFINITY) != 0)

                   || (Double.compare(tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][1]), firstSlope) != 0
                        && Double.compare(tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][1]),
                        Double.NEGATIVE_INFINITY) != 0)

                   || (Double.compare(tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][0]), firstSlope) != 0
                        && Double.compare(tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][0]),
                        Double.NEGATIVE_INFINITY) != 0)) {
                    break;
                }
                j++;
            }

            tmpLineSegments[countOfLineSegments] =
                    new LineSegment(tmpPointSegments[i][0],
                            tmpPointSegments[j - 1][1]);
            countOfLineSegments++;
        }

        segments = new LineSegment[countOfLineSegments];
        for (int k = 0; k < countOfLineSegments; k++)
            segments[k] = tmpLineSegments[k];
    }

    /**
     * Return the number of line segments.
     *
     * @return the number of line segments
     */
    public int numberOfSegments() {
        return segments.length;
    }

    /**
     * Return the line segments.
     *
     * @return the line segments
     */
    public LineSegment[] segments() {
        LineSegment[] outputSegments = new LineSegment[segments.length];
        for (int i = 0; i < segments.length; i++) {
            outputSegments[i] = segments[i];
        }
        return outputSegments;
    }

    /**
     * Unit tests the BruteCollinearPoints data type.
     *
     * @param args
     */
    public static void main(String[] args) {
        int n = StdIn.readInt();
        Point[] points = new Point[n];
        for (int i = 0; i < n; i++) {
            int x = StdIn.readInt();
            int y = StdIn.readInt();
            points[i] = new Point(x, y);
        }

        // draw the points
        StdDraw.enableDoubleBuffering();
        StdDraw.setXscale(0, 32768);
        StdDraw.setYscale(0, 32768);
        for (Point p : points) {
            p.draw();
        }
        StdDraw.show();

        // print and draw the line segments
        BruteCollinearPoints collinear = new BruteCollinearPoints(points);
        for (LineSegment segment : collinear.segments()) {
            StdOut.println(segment);
            segment.draw();
        }
        StdDraw.show();
    }
}
