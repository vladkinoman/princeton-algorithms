import edu.princeton.cs.algs4.Digraph;
import edu.princeton.cs.algs4.BreadthFirstDirectedPaths;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

/**
 * The {@code SAP} class provides methods
 * for finding a shortest ancestral path between two vertices,
 * or two vertices from two different subsets.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class SAP {

    private final Digraph g;
    private final int n;

    /**
     * Initializes {@code SAP} with a digraph (not necessarily a DAG).
     * @param G digraph
     */
    public SAP(Digraph G) {
        if (G == null) 
            throw new IllegalArgumentException("argument is null");
        g = new Digraph(G);
        n = g.V();
    }

    private class LAStructure {
        public int length = -1;
        public int ancestor = -1;
    }

    private LAStructure getLengthAndAncestor(int v, int w) {
        LAStructure result = new LAStructure();
        if (v == w) {
            result.length = 0;
            result.ancestor = v;
            return result;
        }

        int root = -1;
        int rountCounter = 0;
        for (int i = 0; i < n; i++) {
            if (g.outdegree(i) == 0) {
                root = i;
                rountCounter++;
            }
            if (rountCounter > 1) {
                root = -1;
                break;
            }
        }

        BreadthFirstDirectedPaths bfsOfV = new BreadthFirstDirectedPaths(g, v);
        BreadthFirstDirectedPaths bfsOfW = new BreadthFirstDirectedPaths(g, w);
        
        if (root != -1) {
            for (int x: bfsOfV.pathTo(root)) {
                if (bfsOfW.hasPathTo(x)) {
                    int currlength = bfsOfV.distTo(x) + bfsOfW.distTo(x); 
                    if (result.length == -1 || result.length > currlength) {
                        result.ancestor = x;
                        result.length = currlength;
                    }
                }
            }
        } else {
            // Not a rooted DAG. Don't know what to do with this situation yet.
            for (int i = 0; i < n; i++) {
                if (!bfsOfV.hasPathTo(i)) continue;
                Iterable<Integer> it = bfsOfV.pathTo(i);
                for (int x: it) {
                    if (bfsOfW.hasPathTo(x)) {
                        int currlength = bfsOfV.distTo(x) + bfsOfW.distTo(x); 
                        if (result.length == -1 || result.length > currlength) {
                            result.ancestor = x;
                            result.length = currlength;
                        }
                    }
                }
            }
        }
        
        return result;
    }

    private LAStructure getLengthAndAncestorForEachPair(Iterable<Integer> v,
     Iterable<Integer> w) {
        LAStructure result = new LAStructure();
        for (int vv : v) {
            for (int ww : w) {
                LAStructure curr = getLengthAndAncestor(vv, ww);
                if (result.length == -1 || result.length > curr.length) {
                    result.length = curr.length;
                    result.ancestor = curr.ancestor;
                }
            }
        }
        return result;
    }

    private void validateVertex(int v) {
        if (v < 0 || v >= n)
            throw new IllegalArgumentException("vertex " + v +
             " is not between 0 and " + (n-1));
    }

    private void validateVertices(Iterable<Integer> vertices) {
        if (vertices == null) {
            throw new IllegalArgumentException("argument is null");
        }
        for (int v : vertices) {
            validateVertex(v);
        }
    }

    /**
     * Returns length of shortest ancestral path between vertices v and w;
     *  -1 if no such path.
     * @param v vertex
     * @param w vertex
     * @return length of sap between v and w; -1 if no such path
     * @throws IllegalArgumentException unless {@code 0 <= v < V}
     */
    public int length(int v, int w) {
        validateVertex(v);
        validateVertex(w);
        return getLengthAndAncestor(v, w).length;
    }
 
    /** 
     * Returns a common ancestor of v and w that participates in a shortest
     *  ancestral path; -1 if no such path.
     * @param v vertex
     * @param w vertex
     * @return a common ancestor of v and w that participates in a sap;
     *  -1 if no such path
     * @throws IllegalArgumentException unless {@code 0 <= v < V}
     */
    public int ancestor(int v, int w) {
        validateVertex(v);
        validateVertex(w);
        return getLengthAndAncestor(v, w).ancestor;
    }
    
    /**
     * Returns length of shortest ancestral path between any vertex in v and
     *  any vertex in w; -1 if no such path.
     * @param v subset of vertices you can iterate through
     * @param w subset of vertices you can iterate through
     * @return length of sap between any v and w; -1 if no such path
     * @throws IllegalArgumentException unless {@code v != null} or
     *  {@code 0 <= v < V}
     */
    public int length(Iterable<Integer> v, Iterable<Integer> w) {
        validateVertices(v);
        validateVertices(w);
        return getLengthAndAncestorForEachPair(v, w).length;
    }
 
    /**
     * Returns a common ancestor that participates in shortest ancestral path; 
     * -1 if no such path
     * @param v subset of vertices you can iterate through
     * @param w subset of vertices you can iterate through
     * @return a common ancestor of v and w that participates in a sap;
     *  -1 if no such path
     * @throws IllegalArgumentException unless {@code v != null} or
     *  {@code 0 <= v < V}
     */
    public int ancestor(Iterable<Integer> v, Iterable<Integer> w) {
        validateVertices(v);
        validateVertices(w);
        return getLengthAndAncestorForEachPair(v, w).ancestor;
    }
 
    /**
     * Test client for WordNet.
     * 
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        In in = new In(args[0]);
        Digraph G = new Digraph(in);
        SAP sap = new SAP(G);
        while (!StdIn.isEmpty()) {
            int v = StdIn.readInt();
            int w = StdIn.readInt();
            int length   = sap.length(v, w);
            int ancestor = sap.ancestor(v, w);
            StdOut.printf("length = %d, ancestor = %d\n", length, ancestor);
        }
    }
 }