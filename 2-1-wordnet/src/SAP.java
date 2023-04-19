public class SAP {

    // constructor takes a digraph (not necessarily a DAG)
    public SAP(Digraph G)
 
    // length of shortest ancestral path between v and w; -1 if no such path
    public int length(int v, int w)
 
    // a common ancestor of v and w that participates in a shortest ancestral path; -1 if no such path
    public int ancestor(int v, int w)
 
    // length of shortest ancestral path between any vertex in v and any vertex in w; -1 if no such path
    public int length(Iterable<Integer> v, Iterable<Integer> w)
 
    // a common ancestor that participates in shortest ancestral path; -1 if no such path
    public int ancestor(Iterable<Integer> v, Iterable<Integer> w)
 
    // do unit testing of this class
    public static void main(String[] args)
 }