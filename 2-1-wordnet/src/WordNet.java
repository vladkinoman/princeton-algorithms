import java.util.ArrayList;
import java.util.List;
import edu.princeton.cs.algs4.Digraph;
import edu.princeton.cs.algs4.Topological;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.In;

/**
 * The {@code WordNet} class provides methods
 * for creating and analysing a digraph where each vertex v is an integer 
 * that represents a synset, and each directed edge v→w 
 * represents that w is a hypernym of v. 
 
 * The {@code WordNet} digraph is a rooted DAG: it is acyclic and has one
 *  vertex—the root—that is an ancestor of every other vertex. 
 * However, it is not necessarily a tree because a synset can have more
 *  than one hypernym.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class WordNet {
    private final Digraph g;
    private final String[] aSynsets;
    private final List<Integer> lSynsetsIDs;
    private final List<String> lNouns;

    /**
     * Constructs a rooted DAG based on the input data from two files,
     *  synsets and hypernyms.
     * @param synsets path to the input file which contains synsets
     * @param hypernyms path the input file which contains the hypernym
     * relationships
     * @throws IllegalArgumentException if one of the arguments is null, or
     * the input to the constructor does not correspond to a rooted DAG
     */
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

        Topological top = new Topological(g);
        if (!top.hasOrder())
            throw new IllegalArgumentException("Not a rooted DAG");
        int rootCounter = 0;
        int V = g.V();
        for (int i = 0; i < V; i++) {
            if (g.outdegree(i) == 0 && ++rootCounter > 1)
                throw new IllegalArgumentException("Not a rooted DAG");
        }
    }
 
    /**
     * Returns all the nouns of the {@code WordNet}.
     * 
     * @return all the nouns (as an interable)
     */
    public Iterable<String> nouns() {
        return lNouns;
    }
 
    /**
     * Returns a boolean value which is true if the word a {@code WordNet} noun.
     * 
     * @param word word
     * @return {@code true} if the word is a noun, {@code false} otherwise
     * @throws IllegalArgumentException unless {@code word != null}
     */
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

    /**
     * Returns an integer value which corresponds to the distance between
     *  nounA and nounB.
     * @param nounA noun from the {@code WordNet} digraph
     * @param nounB noun from the {@code WordNet} digraph
     * @return distance between nounA and nounB in a sap
     * @throws IllegalArgumentException unless all of the input values
     *  are nouns from the {@code WordNet} digraph
     */
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
 
    /**
     * Returns a synset (second field of synsets.txt) that is the common
     * ancestor of nounA and nounB in a shortest ancestral path.
     * @param nounA from the {@code WordNet} digraph
     * @param nounB from the {@code WordNet} digraph
     * @return synset that is the common ancestor of nounA and nounB in a sap
     * @throws IllegalArgumentException unless all of the input values
     *  are nouns from the {@code WordNet} digraph
     */
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
 
    /**
     * Test client for WordNet.
     * 
     * @param args the command-line arguments
     */
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
 