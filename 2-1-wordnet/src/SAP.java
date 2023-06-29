import edu.princeton.cs.algs4.Digraph;
import edu.princeton.cs.algs4.BreadthFirstDirectedPaths;
import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

public class SAP {

    private final Digraph g;
    // constructor takes a digraph (not necessarily a DAG)
    // E + V
    public SAP(Digraph G) {
        if (G == null) 
            throw new IllegalArgumentException("argument is null");
        g = G;
    }

    private class LAStructure {
        public int ancestor = -1;
        public int length = -1;
    }

    private LAStructure getLengthAndAncestor(int v, int w) {
        // V+E
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
            int V = g.V();
            for (int i = 0; i < V; i++) {
                if (g.outdegree(i) == 0) {
                    root = i;
                    break;
                }
            }
            for(int x: bfsOfV.pathTo(root)) {
                if (bfsOfW.hasPathTo(x) ) {
                    result.ancestor = x;
                    result.length = bfsOfV.distTo(x) + bfsOfW.distTo(x);
                    break;
                }
            }
        }

        return result;
    }

    // throw an IllegalArgumentException unless {@code 0 <= v < V}
    private void validateVertex(int v) {
        int V = g.V();
        if (v < 0 || v >= V)
            throw new IllegalArgumentException("vertex " + v + " is not between 0 and " + (V-1));
    }

    // throw an IllegalArgumentException unless {@code 0 <= v < V}
    private void validateVertices(Iterable<Integer> vertices) {
        if (vertices == null) {
            throw new IllegalArgumentException("argument is null");
        }
        int V = g.V();
        for (int v : vertices) {
            if (v < 0 || v >= V) {
                throw new IllegalArgumentException("vertex " + v + " is not between 0 and " + (V-1));
            }
        }
    }

    // length of shortest ancestral path between v and w; -1 if no such path
    // E + V
    public int length(int v, int w) {
        validateVertex(v);
        validateVertex(w);
        return getLengthAndAncestor(v, w).length;
    }
 
    // a common ancestor of v and w that participates in a shortest ancestral path; -1 if no such path
    // E + V
    public int ancestor(int v, int w) {
        validateVertex(v);
        validateVertex(w);
        return getLengthAndAncestor(v, w).ancestor;
    }
 
    // length of shortest ancestral path between any vertex in v and any vertex in w; -1 if no such path
    // E + V
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
 
    // a common ancestor that participates in shortest ancestral path; -1 if no such path
    // E + V
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
 
    // do unit testing of this class
    /**
     * @param args
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