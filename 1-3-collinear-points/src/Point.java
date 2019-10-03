import java.util.Comparator;
import edu.princeton.cs.algs4.StdDraw;

public class Point implements Comparable<Point> {
    private final int x;     // x-coordinate of this point
    private final int y;     // y-coordinate of this point

    /**
     * Initializes a new point.
     *
     * @param  x the <em>x</em>-coordinate of the point
     * @param  y the <em>y</em>-coordinate of the point
     */
    @SuppressWarnings("checkstyle:MagicNumber")
    public Point(int x, int y) {
        if (x < 0 || x > 32767 || y < 0 || y > 32767)
            throw new IllegalArgumentException();
        /* DO NOT MODIFY */
        this.x = x;
        this.y = y;
    }

    /**
     * Draws this point to standard draw.
     */
    public void draw() {
        /* DO NOT MODIFY */
        StdDraw.point(x, y);
    }

    /**
     * Draws the line segment between this point and the specified point
     * to standard draw.
     *
     * @param that the other point
     */
    public void drawTo(Point that) {
        /* DO NOT MODIFY */
        StdDraw.line(this.x, this.y, that.x, that.y);
    }

    /**
     * Returns the slope between this point and the specified point.
     * Formally, if the two points are (x0, y0) and (x1, y1), then the slope
     * is (y1 - y0) / (x1 - x0). For completeness, the slope is defined to be
     * +0.0 if the line segment connecting the two points is horizontal;
     * Double.POSITIVE_INFINITY if the line segment is vertical;
     * and Double.NEGATIVE_INFINITY if (x0, y0) and (x1, y1) are equal.
     *
     * @param  that the other point
     * @return the slope between this point and the specified point
     */
    public double slopeTo(Point that) {
        if      (this.x == that.x && this.y == that.y)
            return Double.NEGATIVE_INFINITY;
        else if (this.x != that.x && this.y == that.y)
            return +0.0;
        else if (this.x == that.x && this.y != that.y)
            return Double.POSITIVE_INFINITY;
        return (double) (that.y - this.y) / (that.x - this.x);
    }

    /**
     * Compares two points by y-coordinate, breaking ties by x-coordinate.
     * Formally, the invoking point (x0, y0) is less than the argument point
     * (x1, y1) if and only if either y0 < y1 or if y0 = y1 and x0 < x1.
     *
     * @param  that the other point
     * @return the value <tt>0</tt> if this point is equal to the argument
     *         point (x0 = x1 and y0 = y1);
     *         a negative integer if this point is less than the argument
     *         point; and a positive integer if this point is greater than the
     *         argument point
     */
    public int compareTo(Point that) {
        if      (this.y < that.y || this.y == that.y && this.x < that.x)
            return -1;
        else if (this.y > that.y || this.y == that.y && this.x > that.x)
            return 1;
        return 0;
    }

    /**
     * Compares two points by the slope they make with this point.
     * The slope is defined as in the slopeTo() method.
     *
     * @return the Comparator that defines this ordering on points
     */
    public Comparator<Point> slopeOrder() {
        return new BySlope(this);
    }

    private static class BySlope implements Comparator<Point> {
        private final Point thisPoint;

        public BySlope(Point point) {
            thisPoint = point;
        }

        /*
         * The slopeOrder() method should return a comparator that compares
         * its two argument points by the slopes they make with the invoking
         * point (x0, y0). Formally, the point (x1, y1) is less than the point
         * (x2, y2) if and only if the slope (y1 − y0) / (x1 − x0) is less than
         * the slope (y2 − y0) / (x2 − x0).
         * Treat horizontal, vertical, and degenerate line segments as in the slopeTo() method.
         */
        @Override
        public int compare(Point p, Point q) {
            double slope0with1 = thisPoint.slopeTo(p);
            double slope0with2 = thisPoint.slopeTo(q);
            if      (slope0with1 < slope0with2) return -1;
            else if (slope0with1 > slope0with2) return 1;
            return 0;
        }
    }

    /**
     * Returns a string representation of this point.
     * This method is provide for debugging;
     * your program should not rely on the format of the string representation.
     *
     * @return a string representation of this point
     */
    public String toString() {
        /* DO NOT MODIFY */
        return "(" + x + ", " + y + ")";
    }

    /**
     * Unit tests the Point data type.
     */
    public static void main(String[] args) {
    }
}
