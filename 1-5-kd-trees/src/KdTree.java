import java.util.ArrayList;
import java.util.List;
import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.StdDraw;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;

/**
 * The {@code KdTree} represents a data type to represent a set of points in
 * the unit square (all points have x- and y-coordinates between 0 and 1)
 * It supports:
 * <ul>
 * <li>an eﬃcient range search to ﬁnd all of the points contained in a query
 * rectangle.
 * <li>a nearest-neighbor search to ﬁnd a closest point to a query point.
 * </ul>
 * <p>
 * This implementation uses a 2d-tree with a static nested class for
 * tree nodes.
 * <p>
 * 2d-trees have numerous applications, ranging from classifying astronomical
 * objects to computer animation to speeding up neural networks to mining data
 * to image retrieval.
 * 
 * @author Vlad Beklenyshchev aka vladkinoman
 * 
 */
public class KdTree {

    private static class Node {
        private Point2D p;
        private Node lb;
        private Node rt;
        private final RectHV rect;

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

    /**
     * Is the set empty?
     * 
     * @return {@code true} if the tree is empty,
     *         {@code false} otherwise
     */
    public boolean isEmpty() {
        return size() == 0;
    }

    /**
     * Number of points in the set
     * 
     * @return number of points in the set
     */
    public int size() {
        return size(root);
    }

    private int size(Node curr) {
        if (curr == null)
            return 0;
        return 1 + size(curr.lb) + size(curr.rt);
    }

    /**
     * Does the set contain point p?
     * <p>
     * Running time: log N
     * 
     * @param p the point that we want to know if it is in the tree
     * @return {@code true} if the tree contains point p,
     *         {@code false} otherwise
     */
    public boolean contains(Point2D p) {
        if (p == null)
            throw new IllegalArgumentException();
        Node x = root;
        boolean doWeUseXAsKey = true;
        // we don't need a recursive version here,
        // b/c we don't need to update links on the way up
        while (x != null) {
            if (x.p.equals(p))
                return true;
            int cmp = 0;
            if (doWeUseXAsKey) {
                // | x is fixed
                cmp = Double.compare(p.x(), x.p.x());
            } else {
                // — y is fixed
                cmp = Double.compare(p.y(), x.p.y());
            }
            if (cmp < 0)
                x = x.lb;
            else
                x = x.rt;

            doWeUseXAsKey = !doWeUseXAsKey;
        }
        return false;
    }

    /**
     * Add the point to the set (if it is not already in the set)
     * <p>
     * Running time: log N
     * 
     * @param p the point we want to insert
     */
    public void insert(Point2D p) {
        if (p == null)
            throw new IllegalArgumentException();
        root = insert(root, p, new RectHV(0.0, 0.0, 1.0, 1.0), true);
    }

    private Node insert(Node curr, Point2D newp, RectHV rect,
            boolean doWeUseXAsKey) {
        if (curr == null)
            return new Node(newp, rect);
        if (curr.p.equals(newp))
            return curr;

        int cmp = 0;
        RectHV newRect = null;
        if (doWeUseXAsKey) {
            // | x is fixed
            cmp = Double.compare(newp.x(), curr.p.x());
            if (cmp < 0) {
                newRect = new RectHV(rect.xmin(), rect.ymin(), curr.p.x(), rect.ymax());
            } else {
                newRect = new RectHV(curr.p.x(), rect.ymin(), rect.xmax(), rect.ymax());
            }
        } else {
            // — y is fixed
            cmp = Double.compare(newp.y(), curr.p.y());
            if (cmp < 0) {
                newRect = new RectHV(rect.xmin(), rect.ymin(), rect.xmax(), curr.p.y());
            } else {
                newRect = new RectHV(rect.xmin(), curr.p.y(), rect.xmax(), rect.ymax());
            }
        }

        if (cmp < 0)
            curr.lb = insert(curr.lb, newp, newRect, !doWeUseXAsKey);
        else
            curr.rt = insert(curr.rt, newp, newRect, !doWeUseXAsKey);

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
     * 
     * @param curr          current node that is being checked
     * @param doWeUseXAsKey true => | we are using x as a key (it's fixed)
     *                      <p>
     *                      false=> — we are using y as a key (it's fixed)
     */
    private void draw(Node curr, boolean doWeUseXAsKey) {
        if (curr == null)
            return;

        StdDraw.setPenColor(StdDraw.BLACK);
        StdDraw.setPenRadius(0.01);
        StdDraw.point(curr.p.x(), curr.p.y());
        StdDraw.setPenRadius();
        if (doWeUseXAsKey) {
            // | x is fixed
            StdDraw.setPenColor(StdDraw.RED);
            StdDraw.line(curr.p.x(), curr.rect.ymin(),
                    curr.p.x(), curr.rect.ymax());
        } else {
            // — y is fixed
            StdDraw.setPenColor(StdDraw.BLUE);
            StdDraw.line(curr.rect.xmin(), curr.p.y(),
                    curr.rect.xmax(), curr.p.y());
        }
        draw(curr.lb, !doWeUseXAsKey);
        draw(curr.rt, !doWeUseXAsKey);
    }

    private void buildList(Node curr, RectHV that, List<Point2D> lPointsInRange) {
        if (curr == null || !curr.rect.intersects(that))
            return;
        buildList(curr.lb, that, lPointsInRange);
        if (that.contains(curr.p))
            lPointsInRange.add(curr.p);
        buildList(curr.rt, that, lPointsInRange);
    }

    /**
     * All points that are inside the rectangle (or on the boundary)
     * <p>
     * Running time: R + log N, where R is the number of intersections
     * 
     * @param rect the rectangle (or range) which might have some points from the
     *             tree
     * @return the points from the given range
     */
    public Iterable<Point2D> range(RectHV rect) {
        if (rect == null)
            throw new IllegalArgumentException();
        List<Point2D> lPointsInRange = new ArrayList<>();
        buildList(root, rect, lPointsInRange);
        return lPointsInRange;
    }

    /**
     * Pruning rule:
     * if the closest point discovered so far is closer than the distance
     * between the query point and the rectangle corresponding to a node,
     * there is no need to explore that node (or its subtrees).
     * That is,
     * search a node only only if it might contain a point that is closer than
     * the best one found so far.
     * 
     * @param curr    current node that is being checked
     * @param queryp  the point to which we are looking for the closest point
     * @param closest the current best point which is close to queryp
     * @return
     */
    private Point2D nearest(Node curr, Point2D queryp, Point2D closest) {
        double dQuerypToClosest = queryp.distanceSquaredTo(closest);
        // the pruning rule:
        if (curr == null || curr.rect.distanceSquaredTo(queryp) > dQuerypToClosest)
            return closest;

        if (curr.p.distanceSquaredTo(queryp) < dQuerypToClosest)
            closest = curr.p;

        Point2D closestInLB = nearest(curr.lb, queryp, closest);
        double dQuerypToClosestInLB = queryp.distanceSquaredTo(closestInLB);
        Point2D closestInRT = nearest(curr.rt, queryp, closest);
        double dQuerypToClosestInRT = queryp.distanceSquaredTo(closestInRT);

        if      (dQuerypToClosestInLB <= dQuerypToClosestInRT 
            && dQuerypToClosestInLB < dQuerypToClosest) closest = closestInLB;
        else if (dQuerypToClosestInRT <= dQuerypToClosestInLB 
            && dQuerypToClosestInRT < dQuerypToClosest) closest = closestInRT;

        return closest;
    }

    /**
     * A nearest neighbor in the set to point p; null if the set is empty
     * <p>
     * Running time: log N in the best case
     * 
     * @param to the point to which we are looking for the closest one
     * @return the point which is the nearest to to
     */
    public Point2D nearest(Point2D to) {
        if (to == null)
            throw new IllegalArgumentException();
        return root != null ? nearest(root, to, root.p) : null;
    }

    /**
     * Unit testing of the methods (optional)
     * 
     * @param args the arguments that are passed to the program
     */
    public static void main(String[] args) {
        String filename = args[0];
        In in = new In(filename);
        KdTree ps = new KdTree();
        
        while (!in.isEmpty()) {
            double x = in.readDouble();
            double y = in.readDouble();
            Point2D p = new Point2D(x, y);
            ps.insert(p);
        }
        StdOut.printf("size: " + ps.size() + "\n");

        Point2D to = new Point2D(0.864, 0.565);
        Point2D nearest = ps.nearest(to);
        StdOut.printf(nearest.toString() + " is close to " +
                to.toString() + "\n");
        StdOut.printf(nearest.distanceSquaredTo(to) + "\n");
        
        // nearest()           = (0.785, 0.725)
        // distanceSquaredTo() = 0.031841
        // ps.insert(new Point2D(0.372, 0.497)); // -> r v
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.564, 0.413)); // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.226, 0.577)); // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.144, 0.179)); // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.083, 0.51));
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.32, 0.708));  // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.417, 0.362)); // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.862, 0.825));
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.785, 0.725));
        // StdOut.printf("size: " + ps.size() + "\n");
        // ps.insert(new Point2D(0.499, 0.208)); // -> r
        // StdOut.printf("size: " + ps.size() + "\n");
        // StdDraw.enableDoubleBuffering();
        // StdDraw.setXscale(0.0, 1.0);
        // StdDraw.setYscale(0.0, 1.0);
        // ps.draw();
        // StdDraw.show();

        // RectHV queryRange = new RectHV(0.1, 0.1, 0.6, 0.8);
        // StdOut.printf("Points in range " + queryRange.toString() + ":\n");
        // for (Point2D p : ps.range(queryRange)) {
        //     StdOut.printf(p.toString() + "\n");
        // }
        
        // Point2D to = new Point2D(0.864, 0.565);
        // Point2D nearest = ps.nearest(to);
        // StdOut.printf(nearest.toString() + " is close to " +
        //         to.toString() + "\n");
        // StdOut.printf(nearest.distanceSquaredTo(to) + "\n");
    }
}
