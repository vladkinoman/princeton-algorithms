import edu.princeton.cs.algs4.StdDraw;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

import java.util.Arrays;
import java.util.Comparator;

public class FastCollinearPoints {
    private final LineSegment[] segments;

    /**
     * Finds all line segments containing 4 points.
     *
     * @param points
     */
    public FastCollinearPoints(Point[] points) {
        // Checking corner cases...
        if (points == null)
            throw new IllegalArgumentException(
                    "Argument of the constructor is NULL.");

        for (Point p : points)
            if (p == null) throw new IllegalArgumentException(
                    "One of the points is NULL");

        for (int i = 0; i < points.length; i++)
            for (int j = i + 1; j < points.length; j++)
                if (points[j].compareTo(points[i]) == 0)
                    throw new IllegalArgumentException(
                            "Two points are equal.");

        int n = points.length;

        Point[][] tmpPointSegments = new Point[n * n][];
        int countOfPointSegments = 0;
        for (int i = 0; i < n; i++) {
            // Think of points[i] as the origin.
            // For each other point, determine the slope it makes with pnts[i].
            // Sort the points according to the slopes they make with pnts[i].
            Arrays.sort(points, i, n, points[i].slopeOrder());

            int countOfCollPoints = 1;
            for (int j = i + 1; j < n;
                 j += countOfCollPoints, countOfCollPoints = 1) {

                double firstSlope = points[i].slopeTo(points[j]);

                for (int k = 1; j + k < n; k++) {
                    // Check if any 3 (or more) adjacent points in the sorted
                    // order have equal slopes with respect to p. If so, these
                    // points, together with p, are collinear.
                    if (points[i].slopeTo(points[j + k]) != firstSlope) {
                        break;
                    }
                    countOfCollPoints++;
                }

                if (countOfCollPoints >= 3) {
                    // Sort the checked points (including origin)
                    // by natural order to select only min (left border)
                    // and max (right border) points.
                    Arrays.sort(points, j, j + countOfCollPoints);

                    Point min;
                    Point max;
                    if (points[i].compareTo(points[j]) < 0) {
                        min = points[i];
                    } else {
                        min = points[j];
                    }

                    if (points[i].compareTo(
                            points[j + countOfCollPoints - 1]) > 0) {
                        max = points[i];
                    } else {
                        max = points[j + countOfCollPoints - 1];
                    }

                    tmpPointSegments[countOfPointSegments] =
                            new Point[]{min, max};

                    countOfPointSegments++;
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

            // Created an inner class for Comparator to avoid the next warning:
            // (Defining a nested class in this program suggests poor design.)
            // Arrays.sort(tmpPointSegments, i, countOfPointSegments,
            //        new BySlopeForTwoDim(tmpPointSegments[i]));

            final int iForComparator = i;
            // Sort by slope. This is the version for the two
            // dimensional array which is represantation of segments.
            Arrays.sort(tmpPointSegments, i, countOfPointSegments,
                new Comparator<Point[]>() {
                    @Override
                    public int compare(Point[] pSegment, Point[] qSegment) {
                        double slope0with1 = tmpPointSegments[iForComparator]
                                [0].slopeTo(pSegment[0]);
                        double slope0with2 = tmpPointSegments[iForComparator]
                                [0].slopeTo(qSegment[0]);
                        if      (slope0with1 < slope0with2) return -1;
                        else if (slope0with1 > slope0with2) return 1;
                        return 0;
                }
            });

            double firstSlope = tmpPointSegments[i][0]
                    .slopeTo(tmpPointSegments[i][1]);

            int j = i + 1;
            while (j < countOfPointSegments) {
                // We want to make sure that the segment being checked
                // enters the tmpPointSegments[i] segment.
                if ((tmpPointSegments[i][0].slopeTo(tmpPointSegments[j][0])
                        != firstSlope && tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][0])
                        != Double.NEGATIVE_INFINITY)
                   || (tmpPointSegments[i][1].slopeTo(tmpPointSegments[j][1])
                        != firstSlope && tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][1])
                        != Double.NEGATIVE_INFINITY)
                   || (tmpPointSegments[i][0].slopeTo(tmpPointSegments[j][1])
                        != firstSlope && tmpPointSegments[i][0]
                        .slopeTo(tmpPointSegments[j][1])
                        != Double.NEGATIVE_INFINITY)
                   || (tmpPointSegments[i][1].slopeTo(tmpPointSegments[j][0])
                        != firstSlope && tmpPointSegments[i][1]
                        .slopeTo(tmpPointSegments[j][0])
                        != Double.NEGATIVE_INFINITY)) {
                    break;
                }
                j++;
            }
            // We don't want to include the last element
            // which already has a different slope.
            j--;
            Arrays.sort(tmpPointSegments, i, j + 1,
                    new Comparator<Point[]>() {
                @Override
                public int compare(final Point[] pSegment,
                                   final Point[] qSegment) {
                    final Point p = pSegment[0];
                    final Point q = qSegment[0];
                    return p.compareTo(q);
                }
            });

            Point right;
            if (tmpPointSegments[i][1]
                    .compareTo(tmpPointSegments[j][1]) > 0) {
                right = tmpPointSegments[i][1];
            } else {
                right = tmpPointSegments[j][1];
            }

            tmpLineSegments[countOfLineSegments] =
                    new LineSegment(tmpPointSegments[i][0], right);
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
     *
     * @param args
     */
    public static void main(String[] args) {
        // In in = new In(args[0]);
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
        FastCollinearPoints collinearFast = new FastCollinearPoints(points);
        for (LineSegment segment : collinearFast.segments()) {
            StdOut.println(segment);
            segment.draw();
        }
        StdDraw.show();
    }
}