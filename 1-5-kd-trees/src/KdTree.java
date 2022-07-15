import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.SET;
import edu.princeton.cs.algs4.ST;
import edu.princeton.cs.algs4.StdDraw;

public class KdTree {

    private static class Node {
    
        public Node(Point2D newp) {
            p = newp;
        }
        private Point2D p;
        private Node lb;
        private Node rt;
        private RectHV rect;
    }

    private Node root;
    /** Construct an empty set of points.
     */
    public KdTree() {
        root = null;
    }

    /** Is the set empty?
     * @return
     */
    public boolean isEmpty() {
        return size() == 0;
    }
    
    /** Number of points in the set
     * @return
     */
    public int size() {
        return size(root);
    }

    private int size(Node curr) {
        if (curr == null) return 0;
        return 1 + size(curr.lb) + size(curr.rt);
    }

    /** Add the point to the set (if it is not already in the set)
     *  Running time: log N
     */
    public void insert(Point2D p) {
        if (p == null) throw new IllegalArgumentException();
        root = insert(root, p, true);
    }

    private Node insert(Node curr, Point2D newp, boolean doWeUseXAsKey) {
        if (curr == null) return new Node(newp);
        
        int cmp = 0;
        if (doWeUseXAsKey) {
            // | x is fixed
            cmp = Double.compare(newp.x(), curr.p.x());
        } else {
            // — y is fixed
            cmp = Double.compare(newp.y(), curr.p.y());
        }

        if (cmp == 0) curr.p  = newp;
        if (cmp < 0)  curr.lb = insert(curr.lb, newp, !doWeUseXAsKey);
        if (cmp > 0)  curr.rt = insert(curr.rt, newp, !doWeUseXAsKey);
        return curr;
    }

    /** Does the set contain point p?
     *  Running time: log N
     * @return
     */
    public boolean contains(Point2D p) {
        if (p == null) throw new IllegalArgumentException();
        Node x = root;
        boolean doWeUseXAsKey = true;
        // we don't need a recursive version here, 
        // b/c we don't need to update links on the way up
        while (x != null) {
            int cmp = 0;
            if (doWeUseXAsKey) {
                // | x is fixed
                cmp = Double.compare(p.x(), x.p.x());
            } else {
                // — y is fixed
                cmp = Double.compare(p.y(), x.p.y());
            }
            if (cmp  < 0) x = x.lb;
            if (cmp  > 0) x = x.rt;
            if (cmp == 0) return true;
            doWeUseXAsKey = !doWeUseXAsKey;
        }
        return false;
    }

    /** Draw all points to standard draw
     * 
     */
    public void draw() {
        draw(root, new Point2D(0.0, 0.0), 
                   new Point2D(1.0, 1.0), true);
    }

    /**
     * 
     * @param curr
     * @param blp bottom left point of the partition
     * @param trp top right point of the partition
     * @param doWeUseXAsKey
     */
    private void draw(Node curr, Point2D blp, Point2D trp, boolean doWeUseXAsKey) {
        if (curr == null) return;
        
        double x = curr.p.x();
        double y = curr.p.y();

        StdDraw.setPenColor(StdDraw.BLACK);
        StdDraw.setPenRadius(0.0205);
        StdDraw.point(x, y);
        StdDraw.setPenRadius();
        if (doWeUseXAsKey) {
            // | x is fixed
            StdDraw.setPenColor(StdDraw.RED);
            StdDraw.line(x, blp.y(), x, trp.y());
            draw(curr.lb, new Point2D(blp.x(), blp.y()),
                          new Point2D(      x, trp.y()), !doWeUseXAsKey);
            draw(curr.rt, new Point2D(      x, blp.y()),
                          new Point2D(trp.x(), trp.y()), !doWeUseXAsKey);
        } else {
            // — y is fixed
            StdDraw.setPenColor(StdDraw.BLUE);
            StdDraw.line(blp.x(), y, trp.x(), y);
            draw(curr.lb, new Point2D(blp.x(), blp.y()),
                          new Point2D(trp.x(),       y), !doWeUseXAsKey);
            draw(curr.rt, new Point2D(blp.x(),       y),
                          new Point2D(trp.x(), trp.y()), !doWeUseXAsKey);
        }
    }

    private class PointsInRange implements Iterable<Point2D> {

        private final List<Point2D> lPointsInRange = new ArrayList<>();

        public PointsInRange(RectHV rect) {
            // inner constructor
            /*for (Point2D p : rbBST) {
                if (rect.contains(p)) lPointsInRange.add(p);    
            }*/
            throw new UnsupportedOperationException();
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
        /*if (to == null) throw new IllegalArgumentException();
        if (size() == 0) return null;
        
        Point2D pMinDist = rbBST.iterator().next();
        for (Point2D curr : rbBST) {
            if (curr.distanceTo(to) < pMinDist.distanceTo(to)) {
                pMinDist = curr;
            }
        }
        return pMinDist;
        */
        throw new UnsupportedOperationException();
    }

    /** Unit testing of the methods (optional)
     * @param args
     */
    public static void main(String[] args) {
        KdTree ps = new KdTree();
        ps.insert(new Point2D(0.7, 0.2));
        ps.insert(new Point2D(0.5, 0.4));
        ps.insert(new Point2D(0.2, 0.3));
        ps.insert(new Point2D(0.4, 0.7));
        ps.insert(new Point2D(0.9, 0.6));
        // draw the points                                                        
        StdDraw.enableDoubleBuffering();                                          
        StdDraw.setXscale(0.0, 1.0);                                              
        StdDraw.setYscale(0.0, 1.0); 
        ps.draw();
        StdDraw.show();
        //System.out.print(ps.nearest(new Point2D(0.5, 0.8)).toString());
    }
}
