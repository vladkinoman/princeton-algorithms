import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.Comparator;

/**
 * Created by vbekl_000 on 11/28/2016.
 */
public class BruteCollinearPoints {
    private int countOfSegments;
    private LineSegment[] segments;

    // finds all line segments containing 4 points
    public BruteCollinearPoints(Point[] points) {
        if (points == null) {
            throw new java.lang.NullPointerException();
        } else {
            for (Point p: points) {
                if (p == null) throw new java.lang.NullPointerException();
            }
        }
        countOfSegments = 0;
        int countOfAllocatedSegments = 4;
        segments = new LineSegment[countOfAllocatedSegments];
        for (int i = 0; i < points.length; i++) {
            for (int j = i + 1; j < points.length; j++) {
                for (int k = j + 1; k < points.length; k++) {
                    for (int l = k + 1; l < points.length; l++) {

                        if (points[i].slopeTo(points[j])
                                == points[i].slopeTo(points[k])
                                && points[i].slopeTo(points[j])
                                == points[i].slopeTo(points[l])) {
                            if (countOfSegments == countOfAllocatedSegments) {
                                segments = realloc(segments);
                                countOfAllocatedSegments = countOfSegments * 2;
                            }
                            Point min = points[i], max = points[l];
                            for (int m = i + 1, n = l - 1; m < i + 4; m++, n--){
                                if (min.compareTo(points[m]) > 0) {
                                    min = points[m];
                                }
                                if (max.compareTo(points[n]) < 0) {
                                    max = points[n];
                                }
                            }
                            segments[countOfSegments++]
                                    = new LineSegment(min, max);
                        }
                    }
                }
            }
        }
        if (countOfSegments < countOfAllocatedSegments) {
            segments = free(segments);
        }
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

    // the number of line segments
    public int numberOfSegments() {
        return countOfSegments;
    }

    // the line segments
    public LineSegment[] segments() {
        LineSegment[] newSegments = new LineSegment[countOfSegments];
        for (int i = 0; i < newSegments.length; i++) {
            newSegments[i] = segments[i];
        }

        for (int i = 0; i < countOfSegments; i++) {
            for (int j = i + 1; j < countOfSegments; j++) {
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
