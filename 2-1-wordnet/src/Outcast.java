import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;

/**
 * The {@code Outcast} class provides the method {@code outcast}
 * which computes the least related noun to the given array of nouns
 * in the WordNet digraph.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class Outcast {
    private final WordNet wordnet;

    /**
     * Initializes {@code Outcast} with the {@code WordNet} object.
     * 
     * @param wordnet the WordNet digraph
     */
    public Outcast(WordNet wordnet) {   
        this.wordnet = wordnet;
    }

    /**
     * Computes an outcast for a given array of WordNet nouns.
     * 
     * @param nouns an array of nouns
     * @return a String value which represents the outcast
     */
    public String outcast(String[] nouns) {
        int indexOfALeastRelated = 0;
        int di = 0;
        int n = nouns.length;
        for (int i = 0; i < n; i++) {
            int curdi = 0;
            for (int j = 0; j < n; j++) {
                if (i == j) continue;
                curdi += wordnet.distance(nouns[i], nouns[j]);
            }
            if (di < curdi) {
                di = curdi;
                indexOfALeastRelated = i;
            }
        }
        return nouns[indexOfALeastRelated];
    }

    /**
     * Test client for Outcast.
     * 
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        WordNet wordnet = new WordNet(args[0], args[1]);
        Outcast outcast = new Outcast(wordnet);
        for (int t = 2; t < args.length; t++) {
            In in = new In(args[t]);
            String[] nouns = in.readAllStrings();
            StdOut.println(args[t] + ": " + outcast.outcast(nouns));
        }
    }
 }