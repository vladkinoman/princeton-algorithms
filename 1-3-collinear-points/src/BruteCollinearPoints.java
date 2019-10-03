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
     * @param points array which consists of objects of the Point data type
     */
    public BruteCollinearPoints(Point[] points) {
        // Checking corner cases...
        if (points == null)
            throw new IllegalArgumentException(
                    "Argument of the constructor is NULL.");

        for (Point p: points)
            if (p == null) throw new IllegalArgumentException(
                    "One of the points is NULL");

        for (int i = 0; i < points.length; i++)
            for (int j = i + 1; j < points.length; j++)
                if (points[j].compareTo(points[i]) == 0)
                    throw new IllegalArgumentException(
                            "Two points are equal.");

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
                    for (int l = k + 1; l < n; l++) {

                        if (points[i].slopeTo(points[j])
                                == points[i].slopeTo(points[k])
                        &&  points[i].slopeTo(points[j])
                                == points[i].slopeTo(points[l])) {
                            // We want to get only two points in the
                            //   segment p->q->r->s - p and s.
                            // I will choose the segment p->s (i->l).
                            // Sure, we can pick s->p segment if we want to.
                            tmpPointSegments[countOfPointSegments] =
                                    new Point[2];
                            tmpPointSegments[countOfPointSegments][0] =
                                    points[i];
                            tmpPointSegments[countOfPointSegments][1] =
                                    points[l];
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
        for (int i = 0; i < countOfPointSegments;) {
            double firstSlope = tmpPointSegments[i][0]
                    .slopeTo(tmpPointSegments[i][1]);

            int j = i + 1;
            while (j < countOfPointSegments && tmpPointSegments[i][0]
                    .slopeTo(tmpPointSegments[j][1]) == firstSlope)
                j++;

            j--;
            tmpLineSegments[countOfLineSegments] =
                    new LineSegment(tmpPointSegments[i][0],
                            tmpPointSegments[j][1]);
            countOfLineSegments++;
            i = j + 1;
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
        return segments;
    }

    /**
     * Unit tests the BruteCollinearPoints data type.
     *
     * @param args
     */
    @SuppressWarnings("checkstyle:MagicNumber")
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
