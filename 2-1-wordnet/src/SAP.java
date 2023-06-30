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

    /**
     * Initializes {@code SAP} with a digraph (not necessarily a DAG).
     * @param G digraph
     */
    public SAP(Digraph G) {
        if (G == null) 
            throw new IllegalArgumentException("argument is null");
        g = G;
    }

    private class LAStructure {
        public int length = -1;
        public int ancestor = -1;
    }

    private LAStructure getLengthAndAncestor(int v, int w) {
        BreadthFirstDirectedPaths bfsOfV = new BreadthFirstDirectedPaths(g, v);
        BreadthFirstDirectedPaths bfsOfW = new BreadthFirstDirectedPaths(g, w);

        LAStructure result = new LAStructure();
        
        if (bfsOfV.hasPathTo(w) && g.adj(w).iterator().hasNext()) {
            result.ancestor = g.adj(w).iterator().next();
            result.length = bfsOfV.distTo(result.ancestor);
        } else if (bfsOfW.hasPathTo(v) && g.adj(v).iterator().hasNext()) {
            result.ancestor = g.adj(v).iterator().next();
            result.length = bfsOfW.distTo(result.ancestor);
        } else {
            int root = 0;
            int n = g.V();
            for (int i = 0; i < n; i++) {
                if (g.outdegree(i) == 0) {
                    root = i;
                    break;
                }
            }
            for (int x: bfsOfV.pathTo(root)) {
                if (bfsOfW.hasPathTo(x)) {
                    result.ancestor = x;
                    result.length = bfsOfV.distTo(x) + bfsOfW.distTo(x);
                    break;
                }
            }
        }

        return result;
    }

    private void validateVertex(int v) {
        if (v < 0 || v >= g.V())
            throw new IllegalArgumentException("vertex " + v + " is not between 0 and " + (g.V()-1));
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
        int length = -1;
        for (int vv : v) {
            for (int ww : w) {
                LAStructure la = getLengthAndAncestor(vv, ww);
                if (length == -1 || length > la.length) {
                    length = la.length;
                }
            }
        }
        return length;
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
        int ancestor = -1;
        int length = -1;
        for (int vv : v) {
            for (int ww : w) {
                LAStructure la = getLengthAndAncestor(vv, ww);
                if (length == -1 || length > la.length) {
                    length = la.length;
                    ancestor = la.ancestor;
                }
            }
        }
        return ancestor;
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