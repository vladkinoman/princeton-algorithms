import java.util.Arrays;
import java.util.Comparator;

public class FastCollinearPoints {

    private int countOfSegments;
    private LineSegment[] segments;

    // finds all line segments containing 4 or more points
    public FastCollinearPoints(Point[] points) {
        /************************* EXCEPTIONS ****************************/
        if (points == null) {
            throw new java.lang.NullPointerException();
        } else {
            for (Point p: points) {
                if (p == null) throw new java.lang.NullPointerException();
            }
        }
        for (int i = 0; i < points.length; i++) {
            Point tmp = points[i];
            for (int j = i + 1; j < points.length; j++) {
                if (points[j].compareTo(tmp) == 0) {
                    throw new java.lang.IllegalArgumentException();
                }
            }
        }
        /******************************************************************/

        countOfSegments = 0;
        int countOfAllocatedSegments = 4;
        segments = new LineSegment[countOfAllocatedSegments];
        Point origin = null;
        Point[] newPoints = new Point[points.length];
        Point[] setOfCollinears = null;
        Point[] adjacences = new Point[points.length];

        for (int i = 0; i < points.length; i++) {
            newPoints[i] = points[i];
        }
        int adj = 0;
        for (int i = 0, k = 0; i < newPoints.length; i++, k = 0) {
            origin = points[i];
            // create new array
            setOfCollinears = new Point[newPoints.length*2];
            // merge sort
            Arrays.sort(newPoints, origin.slopeOrder());
            for (int j = 0; j < newPoints.length - 1; j++) {
                if (origin.compareTo(newPoints[j]) != 0 &&
                        origin.compareTo(newPoints[j+1]) != 0 &&
                        isEqual(origin.slopeOrder(), newPoints[j],
                                newPoints[j+1])) {
                    setOfCollinears[k++] = newPoints[j];
                    setOfCollinears[k++] = newPoints[j+1];
                }
            }

            if (k >= 3) {

                Point min = origin, max = setOfCollinears[0];
                for (int j = 0; j < k; j++) {
                    if (min.compareTo(setOfCollinears[j]) > 0) {
                        min = setOfCollinears[j];
                    }
                    if (max.compareTo(setOfCollinears[j]) < 0) {
                        max = setOfCollinears[j];
                    }
                }

                if (origin.compareTo(max) > 0) {
                    max = origin;
                }

                if (!isExist(adjacences, adj, min)
                        && !isExist(adjacences, adj, max)
                        && !isEqualsSlope(adjacences, adj, min, max)) {
                    if (adj + 2 > adjacences.length) {
                        adjacences = realloc(adjacences);
                    }
                    adjacences[adj++] = min;
                    adjacences[adj++] = max;
                }
            }
        }

        for (int i = 0; i < adj; i+=2) {
            if (countOfSegments == countOfAllocatedSegments) {
                segments = realloc(segments);
                countOfAllocatedSegments = countOfSegments * 2;
            }

            segments[countOfSegments++]
                    = new LineSegment(adjacences[i], adjacences[i+1]);
        }

        if (countOfSegments < countOfAllocatedSegments) {
            segments = free(segments);
        }
    }

    private boolean isExist(Point[] adjacences, int iteration, Point p) {
        for (int j = 0; j < iteration; j++) {
            if (adjacences[j].compareTo(p) == 0) {
                return true;
            }
        }
        return false;
    }

    private boolean isEqualsSlope(Point[] adjacences, int iteration, Point p,
                                  Point q) {
        for (int j = 0; j < iteration; j++) {
            if (adjacences[j].slopeTo(p) == adjacences[j].slopeTo(q)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isEqual(Comparator<Point> c, Point p, Point q) {
        return c.compare(p, q) == 0;
    }

    private LineSegment[] free(LineSegment[] segments) {
        LineSegment[] newSegments = new LineSegment[countOfSegments];
        for (int i = 0; i < newSegments.length; i++) {
            newSegments[i] = segments[i];
        }
        return newSegments;
    }

    private LineSegment[] realloc(LineSegment[] segments) {
        LineSegment[] newSegments = new LineSegment[countOfSegments * 2];
        for (int i = 0; i < segments.length; i++) {
            newSegments[i] = segments[i];
        }
        return newSegments;
    }

    private Point[] realloc(Point[] segments) {
        Point[] newSegments = new Point[segments.length * 2];
        for (int i = 0; i < segments.length; i++) {
            newSegments[i] = segments[i];
        }
        return newSegments;
    }

    public int numberOfSegments() {
        return countOfSegments;
    }

    /**
     * the line segments
     * @return maximal line segment containing 4 (or more) points exactly once
     */
    public LineSegment[] segments() {
        return segments;
    }
}
