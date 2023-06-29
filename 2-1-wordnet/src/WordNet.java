import java.util.ArrayList;
import java.util.List;
import edu.princeton.cs.algs4.Digraph;
import edu.princeton.cs.algs4.Topological;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;

public class WordNet {
    // Your data type should use space linear in the
    // input size (size of synsets and hypernyms files).
    private final Digraph g;
    private final String[] aSynsets;

    private final List<Integer> lSynsetsIDs;
    private final List<String> lNouns;

    // constructor takes the name of the two input files, n lg n
    // I think n lg n means: (synsets + hypernyms) * lg (synsets + hypernyms)
    public WordNet(String synsets, String hypernyms) {
        if (synsets == null || hypernyms == null) 
            throw new IllegalArgumentException("argument is null");

        In in = new In(synsets);
        String[] lines = in.readAllLines();
        
        int n = lines.length;
        aSynsets = new String[n];
        lSynsetsIDs = new ArrayList<>(n);
        lNouns = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            String[] parts = lines[i].split(",");
            int synsetID = Integer.parseInt(parts[0]);
            String[] nouns = parts[1].split(" ");
            for (String noun: nouns) {
                lSynsetsIDs.add(synsetID);
                lNouns.add(noun);
            }
            aSynsets[i] = parts[1];
        }
  
        g = new Digraph(n);
        in = new In(hypernyms);
        lines = in.readAllLines();
        n = lines.length;
        for (int i = 0; i < n; i++) {
            String[] parts = lines[i].split(",");
            int synsetID = Integer.parseInt(parts[0]);
            int m = parts.length;
            for (int j = 1; j < m; j++) {
                int v = Integer.parseInt(parts[j]);
                // an easily spottable cycle
                if (v == synsetID)
                   throw new IllegalArgumentException("Not a rooted DAG");
                g.addEdge(synsetID, v);
            }
        }

        Topological top = new Topological(g); // V + E in the worst case
        if (!top.hasOrder()) // const
            throw new IllegalArgumentException("Not a rooted DAG");
        int rootCounter = 0;
        int V = g.V();
        for (int i = 0; i < V; i++) { // V in the worst case
            if (g.outdegree(i) == 0 && ++rootCounter > 1)
                throw new IllegalArgumentException("Not a rooted DAG");
        }
    }
 
    // returns all WordNet nouns
    public Iterable<String> nouns() {
        return lNouns;
    }
 
    // is the word a WordNet noun? log in the number of nouns
    public boolean isNoun(String word) {
        if (word == null) 
            throw new IllegalArgumentException("argument is null");
        
        for (String noun: nouns()) {
            if (noun.compareTo(noun) == 0) return true;
        }
        return false;
    }

    private void validateNouns(String nounA, String nounB) {
        if (!isNoun(nounA) || !isNoun(nounB))
            throw new IllegalArgumentException("argument is not a noun");
    }
 
    // distance between nounA and nounB
    // linear in the size of the WordNet digraph
    public int distance(String nounA, String nounB) {
        validateNouns(nounA, nounB);
        List<Integer> indicesOfA = new ArrayList<>();
        List<Integer> indicesOfB = new ArrayList<>();
        
        int n = lNouns.size();
        for (int i = 0; i < n; i++) {
            if        (lNouns.get(i).compareTo(nounA) == 0) {
                indicesOfA.add(lSynsetsIDs.get(i));
            } else if (lNouns.get(i).compareTo(nounB) == 0) {
                indicesOfB.add(lSynsetsIDs.get(i));
            }
        }

        return new SAP(g).length(indicesOfA, indicesOfB);
    }
 
    // a synset (second field of synsets.txt) that is the common
    // ancestor of nounA and nounB in a shortest ancestral path
    // linear in the size of the WordNet digraph
    public String sap(String nounA, String nounB) {
        validateNouns(nounA, nounB);
        List<Integer> indicesOfA = new ArrayList<>();
        List<Integer> indicesOfB = new ArrayList<>();
        
        int n = lNouns.size();
        for (int i = 0; i < n; i++) {
            if        (lNouns.get(i).compareTo(nounA) == 0) {
                indicesOfA.add(lSynsetsIDs.get(i));
            } else if (lNouns.get(i).compareTo(nounB) == 0) {
                indicesOfB.add(lSynsetsIDs.get(i));
            }
        }
        
        return aSynsets[new SAP(g).ancestor(indicesOfA, indicesOfB)];
    }
 
    // do unit testing of this class
    public static void main(String[] args) {
        WordNet wordnet = new WordNet(args[0], args[1]);
        for (String noun : wordnet.nouns()) {
            System.out.print(noun + " ");
        }   
        System.out.println();
        int distance   = wordnet.distance("d", "f");
        String synsetWithCA = wordnet.sap("d", "f");
        StdOut.printf("distance = %d, synset = %s\n", distance, synsetWithCA);
    }
 }
 