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
        for (int i = 0; i < points.length; i++) {
            newPoints[i] = points[i];
        }

        for (int i = 0, k = 0; i < points.length; i++, k = 0) {
            origin = points[i];
            // create new array
            setOfCollinears = new Point[points.length];
            // merge sort
            Arrays.sort(newPoints, origin.slopeOrder());
            for (int j = 0; j < points.length - 1; j++) {
                if (origin.compareTo(points[j]) != 0 &&
                        origin.compareTo(points[j+1]) != 0 &&
                        isEqual(origin.slopeOrder(), points[j], points[j+1])) {
                    setOfCollinears[k++] = points[j];
                    setOfCollinears[k++] = points[j+1];
                }
            }
            // including origin:
            if (k >= 3) {

                if (countOfSegments == countOfAllocatedSegments) {
                    segments = realloc(segments);
                    countOfAllocatedSegments = countOfSegments * 2;
                }

                Point min = origin, max = setOfCollinears[k-1];
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

                segments[countOfSegments++]
                        = new LineSegment(min, max);
            }
        }

        if (countOfSegments < countOfAllocatedSegments) {
            segments = free(segments);
        }
    }

    private boolean isExistBySlope(Point[] setOfCollinears, Point origin) {
        for (int i = 0; i < setOfCollinears.length; i++) {
            if (origin.compareTo(setOfCollinears[i]) == 0) {
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

    public int numberOfSegments() {
        return countOfSegments;
    }

    /**
     * the line segments
     * @return maximal line segment containing 4 (or more) points exactly once
     */
    public LineSegment[] segments() {
        LineSegment[] newSegments = new LineSegment[countOfSegments];
        for (int i = 0; i < newSegments.length; i++) {
            newSegments[i] = segments[i];
        }

        // delete duplicates
        for (int i = 0; i < countOfSegments; i++) {
            for (int j = i + 1; j < countOfSegments; j++) {
                // oh.. my eyes
                if (segments[j].toString().equals(segments[i].toString())) {
                    newSegments[i] = null;
                }
            }
        }

        int j = 0;
        segments = new LineSegment[countOfSegments];
        for (int i = 0; i < segments.length; i++) {
            if (newSegments[i] != null) {
                segments[j] = newSegments[i];
                j++;
            }
        }

        LineSegment[] sToReturn = new LineSegment[j];
        for (int i = 0; i < j; i++) {
            sToReturn[i] = segments[i];
        }
        return sToReturn;
    }
}
