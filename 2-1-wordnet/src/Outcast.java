import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;

public class Outcast {
    
    private final WordNet wordnet;
    // constructor takes a WordNet object
    public Outcast(WordNet wordnet) {   
        this.wordnet = wordnet;
    }

    // given an array of WordNet nouns, return an outcast
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