import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.StdDraw;


public class KdTree {

    private static class Node {
        private Point2D p;
        private Node lb;
        private Node rt;
        private RectHV rect;
        public Node(Point2D p, RectHV rect) {
            this.p = p;
            this.rect = rect;
        }
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

    /** 
     *  Add the point to the set (if it is not already in the set)
     *  Running time: log N
     */
    public void insert(Point2D p) {
        if (p == null) throw new IllegalArgumentException();
        root = insert(root, p, new RectHV(.0, .0, 1.0, 1.0), true);
    }

    private Node insert(Node curr, Point2D newp, RectHV rect, 
     boolean doWeUseXAsKey) {
        if (curr == null) return new Node(newp, rect);
        
        int cmp = 0;
        RectHV newRect = null;
        if (doWeUseXAsKey) {
            // | x is fixed
            cmp = Double.compare(newp.x(), curr.p.x());
            if   (cmp  < 0)  {
                newRect = new RectHV(rect.xmin(), rect.ymin(),  curr.p.x(), rect.ymax());
            } else if (cmp  > 0) {
                newRect = new RectHV( curr.p.x(), rect.ymin(), rect.xmax(), rect.ymax());
            }
        } else {
            // — y is fixed
            cmp = Double.compare(newp.y(), curr.p.y());
            if   (cmp  < 0) {
                newRect = new RectHV(rect.xmin(), rect.ymin(), rect.xmax(),  curr.p.y());
            } else if (cmp  > 0) {
                newRect = new RectHV(rect.xmin(),  curr.p.y(), rect.xmax(), rect.ymax());
            }
                
        }
        if (cmp == 0)  curr.p  = newp;
        if (cmp  < 0)  curr.lb = insert(curr.lb, newp, newRect, !doWeUseXAsKey);
        if (cmp  > 0)  curr.rt = insert(curr.rt, newp, newRect, !doWeUseXAsKey);
        
        return curr;
    }


    /** 
     * Draw all points to standard draw
     */
    public void draw() {
        draw(root, true);
    }

    /**
     * 
     * @param curr
     * @param blp bottom left point of the partition
     * @param trp top right point of the partition
     * @param doWeUseXAsKey
     */
    private void draw(Node curr, boolean doWeUseXAsKey) {
        if (curr == null) return;

        StdDraw.setPenColor(StdDraw.BLACK);
        StdDraw.setPenRadius(0.0205);
        StdDraw.point(curr.p.x(), curr.p.y());
        StdDraw.setPenRadius();
        if (doWeUseXAsKey) {
            // | x is fixed
            StdDraw.setPenColor(StdDraw.RED);            
            StdDraw.line(      curr.p.x(), curr.rect.ymin(), 
                               curr.p.x(), curr.rect.ymax());
        } else {
            // — y is fixed
            StdDraw.setPenColor(StdDraw.BLUE);
            StdDraw.line(curr.rect.xmin(),       curr.p.y(), 
                         curr.rect.xmax(),       curr.p.y());
        }
        draw(curr.lb, !doWeUseXAsKey);
        draw(curr.rt, !doWeUseXAsKey);
    }

    private class PointsInRange implements Iterable<Point2D> {

        private final List<Point2D> lPointsInRange = new ArrayList<>();

        public PointsInRange(RectHV that) {
            buildList(root, that);
        }

        private void buildList(Node curr, RectHV that) {
            if (curr == null || !curr.rect.intersects(that)) return;
            buildList(curr.lb, that);
            if (that.contains(curr.p)) lPointsInRange.add(curr.p);
            buildList(curr.rt, that);
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
        for (Point2D p : ps.range(new RectHV(0.1, 0.1, 0.6, 0.8))) {
            System.out.println(p.toString());            
        }
        //System.out.print(ps.nearest(new Point2D(0.5, 0.8)).toString());
    }
}
