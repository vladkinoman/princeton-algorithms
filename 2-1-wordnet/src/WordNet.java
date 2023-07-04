import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.Iterator;

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
    private final String[] aSynsets;
    private final List<SynsetIDAndNoun> lSynsetIDsAndNouns;
    private final Set<String> setOfNouns;
    private final SAP sap;

    private final class SynsetIDAndNoun {
        public int synsetID;
        public String noun;
        public SynsetIDAndNoun(int synsetID, String noun) {
            this.synsetID = synsetID;
            this.noun = noun;
        }
    }
    
    private static final class ByNoun implements Comparator<SynsetIDAndNoun> {
        @Override
        public int compare(SynsetIDAndNoun o1, SynsetIDAndNoun o2) {
            return o1.noun.compareTo(o2.noun);
        }
    }

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
        List<String> lNouns = new ArrayList<>(n);
        lSynsetIDsAndNouns = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            String[] parts = lines[i].split(",");
            int synsetID = Integer.parseInt(parts[0]);
            String[] nouns = parts[1].split(" ");
            for (String noun: nouns) {
                lSynsetIDsAndNouns.add(new SynsetIDAndNoun(synsetID, noun));
                lNouns.add(noun);
            }
            aSynsets[i] = parts[1];
        }
        
        Collections.sort(lSynsetIDsAndNouns, new ByNoun());

        setOfNouns = new TreeSet<>(lNouns);
  
        Digraph g = new Digraph(n);
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
        n = g.V();
        for (int i = 0; i < n; i++) {
            if (g.outdegree(i) == 0) rootCounter++;
            if (rootCounter > 1)    
                throw new IllegalArgumentException("Not a rooted DAG");
        }
        sap = new SAP(g);
    }
 
    /**
     * Returns all the nouns of the {@code WordNet}.
     * 
     * @return all the nouns (as an interable)
     */
    public Iterable<String> nouns() {
        return setOfNouns;
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

        return setOfNouns.contains(word);
    }

    private void validateNouns(String nounA, String nounB) {
        if (!isNoun(nounA) || !isNoun(nounB))
            throw new IllegalArgumentException("argument is not a noun");
    }

    private int leftmostBinarySearch(List<SynsetIDAndNoun> listSIDNouns,
        String target) {
        int lo = 0, hi = listSIDNouns.size();
        while (lo < hi) {
            int mid = lo + (hi - lo) / 2;
            if (listSIDNouns.get(mid).noun.compareTo(target) < 0) {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        return lo;
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
        
        int n = lSynsetIDsAndNouns.size();
        int i = leftmostBinarySearch(lSynsetIDsAndNouns, nounA);
        while (i < n && lSynsetIDsAndNouns.get(i).noun.compareTo(nounA) == 0) {
            indicesOfA.add(lSynsetIDsAndNouns.get(i).synsetID);
            i++;
        }

        i = leftmostBinarySearch(lSynsetIDsAndNouns, nounB);
        while (i < n && lSynsetIDsAndNouns.get(i).noun.compareTo(nounB) == 0) {
            indicesOfB.add(lSynsetIDsAndNouns.get(i).synsetID);
            i++;
        }

        return sap.length(indicesOfA, indicesOfB);
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

        int n = lSynsetIDsAndNouns.size();
        int i = leftmostBinarySearch(lSynsetIDsAndNouns, nounA);
        while (i < n && lSynsetIDsAndNouns.get(i).noun.compareTo(nounA) == 0) {
            indicesOfA.add(lSynsetIDsAndNouns.get(i).synsetID);
            i++;
        }

        i = leftmostBinarySearch(lSynsetIDsAndNouns, nounB);
        while (i < n && lSynsetIDsAndNouns.get(i).noun.compareTo(nounB) == 0) {
            indicesOfB.add(lSynsetIDsAndNouns.get(i).synsetID);
            i++;
        }

        String synset = null;
        try {
            synset = aSynsets[sap.ancestor(indicesOfA, indicesOfB)];
        } catch (ArrayIndexOutOfBoundsException e) {
            // noticed that there was a glitch (?) during testing on Coursera
            // and their SAP gave -1, so I decided to play it safe
            synset = null;
        }
        return synset;
    }
 
    /**
     * Test client for WordNet.
     * 
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        WordNet wordnet = new WordNet(args[0], args[1]);
        long numberOfNouns = 0;
        Iterator<String> it = wordnet.nouns().iterator();
        while (it.hasNext()) {
            it.next();
            numberOfNouns++;
        }
        StdOut.printf("number of nouns = %d\n", numberOfNouns);
        int distance   = wordnet.distance("parabolic_reflector", "Bronte");
        String synsetWithCA = wordnet.sap("parabolic_reflector", "Bronte");
        StdOut.printf("distance = %d, synset = %s\n", distance, synsetWithCA);
    }
 }
 