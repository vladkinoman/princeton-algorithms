import java.util.Iterator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

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

    private void compareLengthsAndSetNewResultIfNeeded(LAStructure result, 
     LAStructure curr) {
        if (result.length == -1 || result.length > curr.length) {
            result.ancestor = curr.ancestor;
            result.length = curr.length;
        }
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

        BreadthFirstDirectedPaths bfsfromv = new BreadthFirstDirectedPaths(g, v);
        BreadthFirstDirectedPaths bfsfromw = new BreadthFirstDirectedPaths(g, w);
        
        LAStructure curr = new LAStructure();
        if (bfsfromv.hasPathTo(w)) {
            curr.ancestor = w;
            curr.length = bfsfromv.distTo(w);
            compareLengthsAndSetNewResultIfNeeded(result, curr);
        }
        if (bfsfromw.hasPathTo(v)) {
            curr.ancestor = v;
            curr.length = bfsfromw.distTo(v);
            compareLengthsAndSetNewResultIfNeeded(result, curr);
        }
        // note that if there is a direct path btw v and w, it doesn't mean
        // that it's the shortest one
        Iterable<Integer> vertices;
        if (root != -1) {
            vertices = bfsfromv.pathTo(root);
        } else {
            // not a rooted DAG
            vertices = IntStream.rangeClosed(0, n-1).boxed()
                .collect(Collectors.toSet());
        }
        for (int i: vertices) {
            if (i == v || i == w) continue;
            // a slightly more complicated condition for the first option,
            // but it is better to achieve a general look
            if (bfsfromv.hasPathTo(i) && bfsfromw.hasPathTo(i)) {
                curr.ancestor = i;
                curr.length = bfsfromv.distTo(i) + bfsfromw.distTo(i); 
                compareLengthsAndSetNewResultIfNeeded(result, curr);
            }
            // there will be no one less
            if (result.length == 2) break;
        }
        
        return result;
    }

    private LAStructure getLengthAndAncestorForEachPair(Iterable<Integer> v,
     Iterable<Integer> w) {
        LAStructure result = new LAStructure();
        for (int vv : v) {
            for (int ww : w) {
                LAStructure curr = getLengthAndAncestor(vv, ww);
                compareLengthsAndSetNewResultIfNeeded(result, curr);
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
        Iterator<Integer> it = vertices.iterator();
        while (it.hasNext()) {
            Integer value = it.next();
            if (value == null)
                throw new IllegalArgumentException("argument is null");
            validateVertex(value);
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