import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.Stopwatch;
import edu.princeton.cs.algs4.SET;

/**
 * The {@code BoggleSolver} represents a data type for determining valid words
 * for a given Boggle board.
 *
 * <p>
 * This implementation uses the {@code TwentySixWayTrie} data structure which is based on
 * 26-way trie. Construction takes time proportional to the number of keys
 * times length of the key (in the worst case, when length of each word is >= 3).
 * The <em>scoreOf</em> method takes time proportional to the length of the key.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class BoggleSolver
{
    private static final int MIN_LENGTH_OF_VALID = 3;
    private final TwentySixWayTrie trie;
    
    /**
     * Initializes the data structure using the given array of strings as the dictionary.
     * (You can assume each word in the dictionary contains only the uppercase letters A through Z.)
     * @param dictionary given array of strings
     */
    public BoggleSolver(String[] dictionary) {
        trie = new TwentySixWayTrie();
        for (String word: dictionary) {
            if (word.length() >= MIN_LENGTH_OF_VALID) {
                switch(word.length()) {
                    case 3: case 4:
                        trie.put(word, 1);
                        break;
                    case 5:
                        trie.put(word, 2);
                        break;
                    case 6:
                        trie.put(word, 3);
                        break;
                    case 7:
                        trie.put(word, 5);
                        break;
                    default:
                        trie.put(word, 11);
                        break;
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
        SET<String> validWords = new SET<>();
        int rows = board.rows();
        int cols = board.cols();
        boolean[][] marked = new boolean[rows][cols];
        char[] s = new char[rows*cols*2]; // *2 is for the case when we have board of Qs
        int curLen = 0;
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                recurFunc(i, j, marked, s, curLen, board, validWords);
            }
        }
        return validWords;
    }

    private void recurFunc(int i, int j, boolean[][] marked, 
     char[] s, int curLen, BoggleBoard board, SET<String> validWords) {
        if (i < 0 || j < 0 || i >= board.rows() || j >= board.cols() 
            || marked[i][j]
            || curLen >= MIN_LENGTH_OF_VALID && !trie.hasKeyWithPrefix(s, curLen)
            ) {
            return;
        }

        char c = board.getLetter(i, j);
        if (c == 'Q') {
            s[curLen++] = 'Q';
            s[curLen++] = 'U';
        } else {
            s[curLen++] = c;
        }

        if (curLen >= MIN_LENGTH_OF_VALID && trie.contains(s, curLen)) {
            validWords.add(new String(s, 0, curLen));
        }
        marked[i][j] = true;
        
        recurFunc(i-1, j-1, marked, s, curLen, board, validWords);
        recurFunc(i-1, j,   marked, s, curLen, board, validWords);
        recurFunc(i-1, j+1, marked, s, curLen, board, validWords);
        recurFunc(i,   j-1, marked, s, curLen, board, validWords);
        recurFunc(i,   j+1, marked, s, curLen, board, validWords);
        recurFunc(i+1, j-1, marked, s, curLen, board, validWords);
        recurFunc(i+1, j,   marked, s, curLen, board, validWords);
        recurFunc(i+1, j+1, marked, s, curLen, board, validWords);

        marked[i][j] = false;
        if (c == 'Q') {
            curLen -= 2;
        } else {
            curLen--;
        }
    }

    /**
     * Returns the score of the given word if it is in the dictionary, zero otherwise.
     * (You can assume the word contains only the uppercase letters A through Z.)
     * @param word given word
     * @return score of the given word if it is in the dictionary, zero otherwise
     */
    public int scoreOf(String word) {
        return trie.get(word);
    }

    /**
     * Test client for BoggleSolver.
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        In in = new In(args[0]);
        String[] dictionary = in.readAllStrings();
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
            double totalElapsedTime = 0.0;
            for (int i = 0; i < 8000; i++) {
                board = new BoggleBoard();
                Stopwatch watch = new Stopwatch();
                solver.getAllValidWords(board);
                totalElapsedTime += watch.elapsedTime();
            }
            StdOut.println("Time: " + totalElapsedTime);    
        }
    }
}
