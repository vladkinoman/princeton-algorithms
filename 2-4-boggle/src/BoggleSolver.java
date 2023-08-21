import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.Stopwatch;
import edu.princeton.cs.algs4.LinearProbingHashST;

/**
 * The {@code BoggleSolver} represents a data type for determining valid words
 * for a given Boggle board.
 *
 * <p>
 * This implementation uses the {@code TrieST} data structure which is based on
 * 256-way trie. Construction takes time proportional to the number of keys
 * times length of the key (in the worst case, when length of each word is >= 3).
 * The <em>scoreOf</em> method takes time proportional to the length of the key.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BoggleSolver
{
    private static final int LENGTH_OF_VALID = 3;
    private final EngAlphabetTrieST<Integer> trieScores;
    private final LinearProbingHashST<String, Integer> prefixes;
    
    /**
     * Initializes the data structure using the given array of strings as the dictionary.
     * (You can assume each word in the dictionary contains only the uppercase letters A through Z.)
     * @param dictionary given array of strings
     */
    public BoggleSolver(String[] dictionary) {
        trieScores = new EngAlphabetTrieST<>();
        prefixes = new LinearProbingHashST<>();
        for (String word: dictionary) {
            if (word.length() >= LENGTH_OF_VALID) {
                switch(word.length()) {
                    case 3: case 4:
                        trieScores.put(word, 1);
                        break;
                    case 5:
                        trieScores.put(word, 2);
                        break;
                    case 6:
                        trieScores.put(word, 3);
                        break;
                    case 7:
                        trieScores.put(word, 5);
                        break;
                    default:
                        trieScores.put(word, 11);
                        break;
                }
                for (int j = word.length(); j > 0; j--) {
                    prefixes.put(word.substring(0, j), 0);
                }
            }
        }
    }

    /**
     * Returns the set of all valid words in the given Boggle board, as an Iterable.
     * @param board given Boggle board
     * @return set of all valid words in the given Boggle board, as an Iterable
     */
    public Iterable<String> getAllValidWords(BoggleBoard board) {
        EngAlphabetTrieSET validWords = new EngAlphabetTrieSET();
        int rows = board.rows();
        int cols = board.cols();
        boolean[][] marked = new boolean[rows][cols];
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                recurFunc(i, j, marked, sb, board, validWords);
            }
        }
        return validWords;
    }

    private void recurFunc(int i, int j, boolean[][] marked, 
     StringBuilder sb, BoggleBoard board, EngAlphabetTrieSET validWords) {
        String s = sb.toString();
        if (i < 0 || j < 0 || i >= board.rows() || j >= board.cols() 
            || marked[i][j]
            || s.length() > 0 && !prefixes.contains(s)
            ) {
            return;
        }

        char c = board.getLetter(i, j);
        if (c == 'Q') {
            sb.append("QU");
        } else {
            sb.append(c);
        }

        s = null;
        int n = sb.length();
        if (n >= LENGTH_OF_VALID) {
            s = sb.toString();
        }
        if (s != null && !validWords.contains(s) && trieScores.contains(s)) {
            validWords.add(s);
        }
        marked[i][j] = true;
        
        recurFunc(i-1, j-1, marked, sb, board, validWords);
        recurFunc(i-1, j,   marked, sb, board, validWords);
        recurFunc(i-1, j+1, marked, sb, board, validWords);
        recurFunc(i,   j-1, marked, sb, board, validWords);
        recurFunc(i,   j+1, marked, sb, board, validWords);
        recurFunc(i+1, j-1, marked, sb, board, validWords);
        recurFunc(i+1, j,   marked, sb, board, validWords);
        recurFunc(i+1, j+1, marked, sb, board, validWords);

        marked[i][j] = false;
        if (c == 'Q') {
            sb.setLength(sb.length() - 2);
        } else {
            sb.setLength(sb.length() - 1);
        }
    }

    /**
     * Returns the score of the given word if it is in the dictionary, zero otherwise.
     * (You can assume the word contains only the uppercase letters A through Z.)
     * @param word given word
     * @return score of the given word if it is in the dictionary, zero otherwise
     */
    public int scoreOf(String word) {
        if (trieScores.contains(word)) {
            return trieScores.get(word);
        }
        return 0;
    }

    /**
     * Test client for BoggleSolver.
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        In in = new In(args[0]);
        String[] dictionary = in.readAllStrings();
        Stopwatch watch = new Stopwatch();
        BoggleSolver solver = new BoggleSolver(dictionary);
        BoggleBoard board = new BoggleBoard(args[1]);
        int choice = Integer.parseInt(args[2]);
        if (choice == 0) {
            int score = 0;
            for (String word : solver.getAllValidWords(board)) {
                StdOut.println(word);
                score += solver.scoreOf(word);
            }
            StdOut.println("Score = " + score);
        } else {
            for (int i = 0; i < 1000; i++) {
                board = new BoggleBoard();
                int score = 0;
                for (String word : solver.getAllValidWords(board)) {
                    StdOut.println(word);
                    score += solver.scoreOf(word);
                }
                StdOut.println("Score = " + score);
            }
        }
        StdOut.println("Time: " + watch.elapsedTime());
    }
}
