public class Point {

    // constructs the point (x, y)
    public Point(int x, int y) {

    }

    // draws this point
    public void draw() {

    }

    // draws the line segment from this point to that point
    public void drawTo(Point that)

    // string representation
    public String toString()

    // compare two points by y-coordinates, breaking ties by x-coordinates
    public int compareTo(Point that)

    // the slope between this point and that point
    public double slopeTo(Point that)

    // compare two points by slopes they make with this point
    public Comparator<Point> slopeOrder() {

    }

    /**
     * Unit tests the Point data type.
     */
    public static void main(String[] args) {
        // read the n points from a file
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
        /*BruteCollinearPoints collinear = new BruteCollinearPoints(points);
        for (LineSegment segment : collinear.segments()) {
            StdOut.println(segment);
            segment.draw();
        }
        StdDraw.show();*/

        FastCollinearPoints collinearFast = new FastCollinearPoints(points);
        for (LineSegment segment : collinearFast.segments()) {
            StdOut.println(segment);
            segment.draw();
        }
        StdDraw.show();
    }
}
