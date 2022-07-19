import edu.princeton.cs.algs4.Point2D;
import edu.princeton.cs.algs4.RectHV;
import edu.princeton.cs.algs4.StdDraw;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.Stopwatch;
import edu.princeton.cs.algs4.Queue;

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
        private int count;
        public Node(Point2D p, RectHV rect, int count) {
            this.p = p;
            this.rect = rect;
            this.count = count;
        }
    }

    private Node root;

    /**
     * Construct an empty set of points.
     */
    public KdTree() {
    }

    /**
     * Is the set empty?
     * 
     * @return {@code true} if the tree is empty,
     *         {@code false} otherwise
     */
    public boolean isEmpty() {
        return root == null;
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
        if (curr == null) return 0;
        return curr.count;
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
            int cmp = 0;
            if (doWeUseXAsKey) {
                // | x is fixed
                cmp = Double.compare(p.x(), x.p.x());
            } else {
                // — y is fixed
                cmp = Double.compare(p.y(), x.p.y());
            }
            if      (cmp < 0)
                x = x.lb;
            else if (cmp == 0 && x.p.equals(p))
                return true;
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

    private Node insert(Node curr, Point2D p, RectHV rect,
            boolean doWeUseXAsKey) {
        if (curr == null)
            return new Node(p, rect, 1);
            
        int cmp = 0;
        RectHV newRect = null;
        if (doWeUseXAsKey) {
            // | x is fixed
            cmp = Double.compare(p.x(), curr.p.x());
            if (cmp < 0) {
                newRect = new RectHV(rect.xmin(), rect.ymin(), curr.p.x(), rect.ymax());
            } else {
                newRect = new RectHV(curr.p.x(), rect.ymin(), rect.xmax(), rect.ymax());
            }
        } else {
            // — y is fixed
            cmp = Double.compare(p.y(), curr.p.y());
            if (cmp < 0) {
                newRect = new RectHV(rect.xmin(), rect.ymin(), rect.xmax(), curr.p.y());
            } else {
                newRect = new RectHV(rect.xmin(), curr.p.y(), rect.xmax(), rect.ymax());
            }
        }

        if      (cmp < 0)
            curr.lb = insert(curr.lb, p, newRect, !doWeUseXAsKey);
        else if (cmp == 0 && curr.p.equals(p))
            curr.p = p;
        else
            curr.rt = insert(curr.rt, p, newRect, !doWeUseXAsKey);

        curr.count = 1 + size(curr.lb) + size(curr.rt);
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
        // inorder traversal
        if (rect == null)
            throw new IllegalArgumentException();
        Queue<Point2D> qPointsInRange = new Queue<>();
        buildQueue(root, rect, qPointsInRange);
        return qPointsInRange;
    }

    private void buildQueue(Node curr, RectHV that, Queue<Point2D> q) {
        if (curr == null || !curr.rect.intersects(that))
            return;
        buildQueue(curr.lb, that, q);
        if (that.contains(curr.p))
            q.enqueue(curr.p);
        buildQueue(curr.rt, that, q);
    }

    /**
     * A nearest neighbor in the set to point p; null if the set is empty
     * <p>
     * Running time: log N in the best case
     * 
     * @param p the point p which we are looking for the closest one
     * @return the point which is the nearest to p
     */
    public Point2D nearest(Point2D p) {
        if (p == null)
            throw new IllegalArgumentException();
        return root != null ? nearest(root, p, root.p, true) : null;
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
     * @param p  the point p which we are looking for the closest point
     * @param closest the current best point which is close to p
     * @return the point which is the nearest to p
     */
    private Point2D nearest(Node curr, Point2D p, Point2D closest, boolean doWeUseXAsKey) {
        double dClosest = p.distanceSquaredTo(closest);
        double dCurr    = p.distanceSquaredTo(curr.p);
        if (dCurr < dClosest) closest = curr.p;

        if (doWeUseXAsKey && p.x() < curr.p.x()
        || !doWeUseXAsKey && p.y() < curr.p.y()) {
            // go to the left/down of the splitting line
            if (curr.lb != null) {
                closest  = nearest(curr.lb, p, closest, !doWeUseXAsKey);
                dClosest = p.distanceSquaredTo(closest);
            }
            // should we check to the right/up of the splitting line?
            if (curr.rt != null && curr.rt.rect.distanceSquaredTo(p) < dClosest) {
                closest  = nearest(curr.rt, p, closest, !doWeUseXAsKey);
            }
        } else {
            // go to the right/up of the splitting line
            if (curr.rt != null) {
                closest = nearest(curr.rt, p, closest, !doWeUseXAsKey);
                dClosest = p.distanceSquaredTo(closest);
            }
            // should we check to the left/down of the splitting line?
            if (curr.lb != null && curr.lb.rect.distanceSquaredTo(p) < dClosest) {
                closest  = nearest(curr.lb, p, closest, !doWeUseXAsKey);
            }
        }

        return closest;
    }

    /**
     * Unit testing of the methods (optional)
     * 
     * @param args the arguments that are passed to the program
     */
    public static void main(String[] args) {
        String filename = args[0];
        In in = new In(filename);
        KdTree kdtree = new KdTree();
        Stopwatch watch = new Stopwatch();
        while (!in.isEmpty()) {
            double x = in.readDouble();
            double y = in.readDouble();
            Point2D p = new Point2D(x, y);
            kdtree.insert(p);
            StdOut.printf("size: " + kdtree.size() + "\n");
            if (kdtree.isEmpty()) throw new UnsupportedOperationException();
        }
        StdOut.printf("elapsed time: " + watch.elapsedTime() + "\n");
        StdOut.printf("size: " + kdtree.size() + "\n");
        // it is in input1M.txt
        Point2D toFind = new Point2D(0.684711, 0.818767);
        StdOut.printf("does it contain " + toFind.toString() + " ? A: " +
         kdtree.contains(toFind) + "\n");
        Point2D p = new Point2D(0.864, 0.565); 
        // should be (0.864377, 0.564852) for input1M.txt
        Point2D nearest = kdtree.nearest(p);
        StdOut.printf(nearest.toString() + " is close to " +
                p.toString() + "\n");
        // should be 1.6403299999994846E-7
        StdOut.printf(nearest.distanceSquaredTo(p) + "\n");

        // For drawing:
        // StdDraw.enableDoubleBuffering();
        // StdDraw.setXscale(0.0, 1.0);
        // StdDraw.setYscale(0.0, 1.0);
        // kdtree.draw();
        // StdDraw.show();

        // Testing nearest
        // correct: A B H I C F 
        // mine:    A B H I C F (F is close)
        // kdtree.insert(new Point2D(0.372, 0.497)); // A
        // kdtree.insert(new Point2D(0.564, 0.413)); // B
        // kdtree.insert(new Point2D(0.226, 0.577)); // C
        // kdtree.insert(new Point2D(0.144, 0.179)); // D
        // kdtree.insert(new Point2D(0.083, 0.51));  // E
        // kdtree.insert(new Point2D(0.32, 0.708));  // F
        // kdtree.insert(new Point2D(0.417, 0.362)); // G
        // kdtree.insert(new Point2D(0.862, 0.825)); // H
        // kdtree.insert(new Point2D(0.785, 0.725)); // I
        // kdtree.insert(new Point2D(0.499, 0.208)); // J
        // Point2D p = new Point2D(0.53, 0.76);
        // Point2D nearest = kdtree.nearest(p);
        // StdOut.printf(nearest.toString() + " is close to " +
        //         p.toString() + "\n");
        // StdOut.printf(nearest.distanceSquaredTo(p) + "\n");

        // A E B D & E is close
        // kdtree.insert(new Point2D(0.7, 0.2)); // A
        // kdtree.insert(new Point2D(0.5, 0.4)); // B
        // kdtree.insert(new Point2D(0.2, 0.3)); // C
        // kdtree.insert(new Point2D(0.4, 0.7)); // D
        // kdtree.insert(new Point2D(0.9, 0.6)); // E
        // Point2D p = new Point2D(0.8, 0.7);
        // Point2D nearest = kdtree.nearest(p);
        // StdOut.printf(nearest.toString() + " is close to " +
        //         p.toString() + "\n");
        // StdOut.printf(nearest.distanceSquaredTo(p) + "\n");
    }
}
