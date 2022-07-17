import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.StdDraw;
import edu.princeton.cs.algs4.StdOut;

/**
 * The {@code KdTree} represents a data type to represent a set of points in
 *  the unit square (all points have x- and y-coordinates between 0 and 1) 
 *  It supports:
 *  <ul>
 *   <li>an eﬃcient range search to ﬁnd all of the points contained in a query rectangle.
 *   <li>a nearest-neighbor search to ﬁnd a closest point to a query point.
 *  </ul>
 * <p>
   This implementation uses a 2d-tree with a static nested class for
 *  tree nodes.
 * <p>
 * 2d-trees have numerous applications, ranging from classifying astronomical
 *  objects to computer animation to speeding up neural networks to mining data
 *  to image retrieval.
 * 
 * @author Vlad Beklenyshchev aka vladkinoman
 
 */
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
    
    /** 
     * Construct an empty set of points.
     */
    public KdTree() {
        root = null;
    }

    /** Is the set empty?
     * @return {@code true}  if the tree is empty,
     *         {@code false} otherwise
     */
    public boolean isEmpty() {
        return size() == 0;
    }
    
    /** Number of points in the set
     * @return number of points in the set
     */
    public int size() {
        return size(root);
    }

    private int size(Node curr) {
        if (curr == null) return 0;
        return 1 + size(curr.lb) + size(curr.rt);
    }

    /** Does the set contain point p?
     *  <p>Running time: log N
     * @param p the point that we want to know if it is in the tree
     * @return {@code true}  if the tree contains point p,
     *         {@code false} otherwise
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
     *  <p>Running time: log N
     *  @param p the point we want to insert 
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
     * Recursively draw points that divide our space.
     * @param curr current node that is being checked
     * @param doWeUseXAsKey true => | we are using x as a key (it's fixed)
     *                   <p>false=> — we are using y as a key (it's fixed)
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
     *  <p>Running time: R + log N, where R is the number of intersections
     * @param rect the rectangle (or range) which might have some points from the tree
     * @return the points from the given range
     */
    public Iterable<Point2D> range(RectHV rect) {
        if (rect == null) throw new IllegalArgumentException();
        return new PointsInRange(rect);
    }

    /**
     * Pruning rule: 
     *  if the closest point discovered so far is closer than the distance
     *  between the query point and the rectangle corresponding to a node,
     *  there is no need to explore that node (or its subtrees).
     * That is,
     *  search a node only only if it might contain a point that is closer than
     *  the best one found so far. 
     * 
     * @param curr current node that is being checked
     * @param queryp the point to which we are looking for the closest point
     * @param closest the current best point which is close to queryp
     * @return
     */
    private Point2D nearest(Node curr, Point2D queryp, Point2D closest) {
        // the pruning rule:
        if (curr == null || curr.rect.distanceTo(queryp) > queryp.distanceTo(closest))
            return closest;

        if (curr.p.distanceTo(queryp) < curr.p.distanceTo(closest)) 
            closest = curr.p;
        
        Point2D closestInLB = nearest(curr.lb, queryp, closest);
        if (closestInLB.distanceTo(queryp) < closest.distanceTo(queryp))
            closest = closestInLB;
        Point2D closestInRT = nearest(curr.rt, queryp, closest);
        if (closestInRT.distanceTo(queryp) < closest.distanceTo(queryp))
            closest = closestInRT;
        
        return closest;
    }

    /** A nearest neighbor in the set to point p; null if the set is empty 
     *  <p>Running time: log N in the best case
     * @param to the point to which we are looking for the closest one
     * @return the point which is the nearest to to
     */
    public Point2D nearest(Point2D to) {
        if (to == null) throw new IllegalArgumentException();
        return root != null ? nearest(root, to, root.p) : null;
    }

    /** Unit testing of the methods (optional)
     * @param args the arguments that are passed to the program
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
        RectHV queryRange = new RectHV(0.1, 0.1, 0.6, 0.8);
        StdOut.printf("Points in range " + queryRange.toString() + ":\n");
        for (Point2D p : ps.range(queryRange)) {
            StdOut.printf(p.toString() + "\n");
        }
        Point2D to = new Point2D(0.3, 0.9);
        StdOut.printf(ps.nearest(to).toString() + " is close to " +
         to.toString() + "\n");
        to         = new Point2D(0.91, 0.8);
        StdOut.printf(ps.nearest(to).toString() + " is close to " +
         to.toString() + "\n");
        to         = new Point2D(0.93, 0.18);
        StdOut.printf(ps.nearest(to).toString() + " is close to " +
          to.toString() + "\n");
    }
}
