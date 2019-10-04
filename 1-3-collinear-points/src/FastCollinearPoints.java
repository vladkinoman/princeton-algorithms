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
            // Sort the points according to the slopes they makes with p[i].
            Arrays.sort(points, i, n, points[i].slopeOrder());

            int countOfCollPoints = 1;
            for (int j = i + 1; j < n;
                 j++, countOfCollPoints = 1) {

                double firstSlope = points[i].slopeTo(points[j]);

                for (int k = 1; j + k < n; k++) {
                    if (points[i].slopeTo(points[j + k]) != firstSlope) {
                        break;
                    }
                    countOfCollPoints++;
                }

                if (countOfCollPoints >= 3) {
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
        for (int i = 0; i < countOfPointSegments; ) {

            Arrays.sort(tmpPointSegments, i, countOfPointSegments,
                    new BySlopeForTwoDim(tmpPointSegments[i]));

            double firstSlope = tmpPointSegments[i][0]
                    .slopeTo(tmpPointSegments[i][1]);

            int j = i + 1;
            while (j < countOfPointSegments) {

                if (tmpPointSegments[i][0].slopeTo(tmpPointSegments[j][0])
                        != firstSlope && tmpPointSegments[i][0]
                        .compareTo(tmpPointSegments[j][0]) != 0
                   && tmpPointSegments[i][0].slopeTo(tmpPointSegments[j][0])
                        != firstSlope && tmpPointSegments[i][0]
                        .compareTo(tmpPointSegments[j][1]) != 0) {
                    break;
                }
                j++;
            }


            j--;
            Arrays.sort(tmpPointSegments, i, j + 1, new Comparator<Point[]>() {
                @Override
                public int compare(final Point[] pSegment,
                                   final Point[] qSegment) {
                    final Point p = pSegment[0];
                    final Point q = qSegment[0];
                    return p.compareTo(q);
                }
            });
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

    private static class BySlopeForTwoDim
            implements Comparator<Point[]> {
        // Array consists of two elements - points (p1, p2)
        private final Point[] thisSegment;

        /**
         * Comparator to sort the two dimensional array of point segments
         * by the slope while checking only the first points of segments.
         *
         * @param segment array which consists of two elements (p1, p2)
         */
        BySlopeForTwoDim(Point[] segment) {
            thisSegment = segment;
        }

        /**
         * Method compare does comparison of the first points of the
         * segments pArr and qArr.
         *
         * @param pArr array of two elements (first segment of points)
         * @param qArr array of two elements (second segment of points)
         * @return
         */
        @Override
        public int compare(Point[] pArr, Point[] qArr) {
            double slope0with1 = thisSegment[0].slopeTo(pArr[0]);
            double slope0with2 = thisSegment[0].slopeTo(qArr[0]);
            if      (slope0with1 < slope0with2) return -1;
            else if (slope0with1 > slope0with2) return 1;
            return 0;
        }
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
    @SuppressWarnings("checkstyle:MagicNumber")
    public static void main(String[] args) {
        //In in = new In(args[0]);
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