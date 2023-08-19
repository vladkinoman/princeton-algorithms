import java.util.Arrays;

import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.TrieST;
import edu.princeton.cs.algs4.TrieSET;
import edu.princeton.cs.algs4.Stopwatch;

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
    private final TrieST<Integer> trieScores;
    private final TrieSET prefixes;
    private static final int LENGTH_OF_VALID = 3;
    
    /**
     * Initializes the data structure using the given array of strings as the dictionary.
     * (You can assume each word in the dictionary contains only the uppercase letters A through Z.)
     * @param dictionary given array of strings
     */
    public BoggleSolver(String[] dictionary) {
        prefixes = new TrieSET();
        trieScores = new TrieST<>();
        for (String word: dictionary) {
            if (word.length() >= LENGTH_OF_VALID) {
                trieScores.put(word, 0);
                for (int j = word.length(); j > 0; j--)
                    prefixes.add(word.substring(0, j));
            }
        }
    }
    /**
     * Returns the set of all valid words in the given Boggle board, as an Iterable.
     * @param board given Boggle board
     * @return set of all valid words in the given Boggle board, as an Iterable
     */
    public Iterable<String> getAllValidWords(BoggleBoard board) {
        TrieSET validWords = new TrieSET();
        int n = board.rows();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                String s = "";
                s = addLetterConsideringQu(board, i, j, s);
                boolean[][] visited = new boolean[n][n];
                visited[i][j] = true;
                searchNeighbours(i, j, visited, s, board, validWords);
            }
        }
        return validWords;
    }
    private String addLetterConsideringQu(BoggleBoard board, int i, int j, 
     String s) {
        char letter = board.getLetter(i, j);
        if (letter == 'Q') {
            s += "QU";
        } else {
            s += letter;
        }
        return s;
    }
    
    // board and validWords are shared objects
    private void searchNeighbours(int i, int j, boolean[][] visited,
     String s, BoggleBoard board, TrieSET validWords) {
        matchPattern(i-1, j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i-1, j,   Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i-1, j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i,   j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i,   j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i+1, j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i+1, j,   Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
        matchPattern(i+1, j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), s, board, validWords);
    }

    private void matchPattern(int i, int j, boolean[][] visited, 
     String s, BoggleBoard board, TrieSET setValidWords) {
        if (i < 0 || j < 0 || i >= visited.length || j >= visited.length 
            || !prefixes.contains(s) || !trieScores.keysWithPrefix(s).iterator().hasNext() || visited[i][j]) {
            return;
        }
        s = addLetterConsideringQu(board, i, j, s);
        visited[i][j] = true;
        int n = s.length();
        if (n >= LENGTH_OF_VALID && !setValidWords.contains(s) 
            && trieScores.contains(s)) {
            switch(n) {
                case 3: case 4:
                    trieScores.put(s, 1);
                    break;
                case 5:
                    trieScores.put(s, 2);
                    break;
                case 6:
                    trieScores.put(s, 3);
                    break;
                case 7:
                    trieScores.put(s, 5);
                    break;
                default:
                    trieScores.put(s, 11);
                    break;
            }
            setValidWords.add(s);
        }
        searchNeighbours(i, j, visited, s, board, setValidWords);
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
        // BoggleBoard board = new BoggleBoard(args[1]);
        // int score = 0;
        // for (String word : solver.getAllValidWords(board)) {
        //     StdOut.println(word);
        //     score += solver.scoreOf(word);
        // }
        // StdOut.println("Score = " + score);
        for (int i = 0; i < 1000; i++) {
            BoggleBoard board = new BoggleBoard();
            int score = 0;
            for (String word : solver.getAllValidWords(board)) {
                StdOut.println(word);
                score += solver.scoreOf(word);
            }
            StdOut.println("Score = " + score);
        }
        StdOut.println("Time: " + watch.elapsedTime());
    }
}
