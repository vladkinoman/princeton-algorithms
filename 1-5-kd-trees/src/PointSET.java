import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.SET;
import edu.princeton.cs.algs4.StdDraw;

public class PointSET {

    private SET<Point2D> rbBST;

    /** Construct an empty set of points.
     */
    public PointSET() {
        rbBST = new SET<>();
    }

    /** Is the set empty?
     * @return
     */
    public boolean isEmpty() {
        return rbBST.isEmpty();
    }
    
    /** Number of points in the set
     * @return
     */
    public int size() {
        return rbBST.size();
    }

    /** Add the point to the set (if it is not already in the set)
     *  Running time: log N
     */
    public void insert(Point2D p) {
        if (p == null) throw new IllegalArgumentException();
        rbBST.add(p);
    }

    /** Draw all points to standard draw
     * 
     */
    public void draw() {
        for (Point2D p : rbBST) {
            StdDraw.point(p.x(), p.y());
        }
    }

    /** Does the set contain point p?
     *  Running time: log N
     * @return
     */
    public boolean contains(Point2D p) {
        if (p == null) throw new IllegalArgumentException();
        return rbBST.contains(p);
    }

    private class PointsInRange implements Iterable<Point2D> {

        private final List<Point2D> lPointsInRange = new ArrayList<>();

        public PointsInRange(RectHV rect) {
            // inner constructor
            for (Point2D p : rbBST) {
                if (rect.contains(p)) lPointsInRange.add(p);    
            }
        }

        @Override
        public Iterator<Point2D> iterator() {
            return lPointsInRange.iterator();
        }

    }

    /** All points that are inside the rectangle (or on the boundary)
     *  Running time: N
     * @param rect
     * @return
     */
    public Iterable<Point2D> range(RectHV rect) {
        if (rect == null) throw new IllegalArgumentException();
        return new PointsInRange(rect);
    }

    /** A nearest neighbor in the set to point p; null if the set is empty 
     *  Running time: N
     * @param p
     * @return
     */
    public Point2D nearest(Point2D to) {
        if (to == null) throw new IllegalArgumentException();
        if (size() == 0) return null;
        
        Point2D pMinDist = rbBST.iterator().next();
        for (Point2D curr : rbBST) {
            if (curr.distanceTo(to) < pMinDist.distanceTo(to)) {
                pMinDist = curr;
            }
        }
        return pMinDist;
    }

    /** Unit testing of the methods (optional)
     * @param args
     */
    public static void main(String[] args) {
        PointSET ps = new PointSET();
        ps.insert(new Point2D(0.1, 0.1));
        ps.insert(new Point2D(0.2, 0.5));
        ps.insert(new Point2D(0.8, 0.9));
        System.out.print(ps.nearest(new Point2D(0.5, 0.8)).toString());
    }
}
