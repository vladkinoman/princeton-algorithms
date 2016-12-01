import java.util.Arrays;

public class FastCollinearPoints {

    private int countOfSegments;
    private LineSegment[] segments;

    // finds all line segments containing 4 or more points
    public FastCollinearPoints(Point[] points) {
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

        countOfSegments = 0;
        int countOfAllocatedSegments = 4;
        segments = new LineSegment[countOfAllocatedSegments];

        Arrays.sort(points, points[0].slopeOrder());
    }

    public int numberOfSegments() {
        return countOfSegments;
    }

    // the line segments
    public LineSegment[] segments() {
        return segments;
    }
}
