import java.util.Arrays;

import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.TrieST;
import edu.princeton.cs.algs4.TrieSET;


public class BoggleSolver
{
    private final TrieST<Integer> stScores;
    private static final int LENGTH_OF_VALID = 3;
    
    /**
     * Initializes the data structure using the given array of strings as the dictionary.
     * (You can assume each word in the dictionary contains only the uppercase letters A through Z.)
     * @param dictionary
     */
    public BoggleSolver(String[] dictionary) {
        stScores = new TrieST<>();
        for (String word: dictionary) {
            if (word.length() >= LENGTH_OF_VALID) {
                stScores.put(word, 0);
            }
        }
    }
    /**
     * Returns the set of all valid words in the given Boggle board, as an Iterable.
     * @param board
     * @return
     */
    public Iterable<String> getAllValidWords(BoggleBoard board) {
        TrieSET validWords = new TrieSET();        
        for (int i = 0; i < 4; i++) {
            for (int j = 0; j < 4; j++) {
                String s = "" + board.getLetter(i, j);
                boolean[][] visited = new boolean[4][4];
                visited[i][j] = true;
                recurrentFunc(i-1, j-1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i-1, j,   Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i-1, j+1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i,   j-1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i,   j+1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i+1, j-1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i+1, j,   Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
                recurrentFunc(i+1, j+1, Arrays.stream(visited).map(boolean[]::clone)
                .toArray(boolean[][]::new), new String(s), board, validWords);
            }
        }
        return validWords;
    }

    private void recurrentFunc(int i, int j, boolean[][] visited, 
        String s, BoggleBoard board, TrieSET validWords) {
        if (i < 0 || j < 0 || i >= visited.length || j>= visited.length 
            || visited[i][j]) {
            return;
        }
        s += board.getLetter(i, j);
        visited[i][j] = true;
        int n = s.length();
        if (n >= LENGTH_OF_VALID && !validWords.contains(s) && 
            stScores.contains(s)) {
            switch(n) {
                case 3: case 4:
                    stScores.put(s, 1);
                    break;
                case 5:
                    stScores.put(s, 2);
                    break;
                case 6:
                    stScores.put(s, 3);
                    break;
                case 7:
                    stScores.put(s, 5);
                    break;
                default:
                    stScores.put(s, 11);
                    break;
            }
            validWords.add(s);
        }
        recurrentFunc(i-1, j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i-1, j,   Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i-1, j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i,   j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i,   j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i+1, j-1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i+1, j,   Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
        recurrentFunc(i+1, j+1, Arrays.stream(visited).map(boolean[]::clone)
        .toArray(boolean[][]::new), new String(s), board, validWords);
    }

    /**
     * Returns the score of the given word if it is in the dictionary, zero otherwise.
     * (You can assume the word contains only the uppercase letters A through Z.)
     * @param word
     * @return
     */
    public int scoreOf(String word) {
        if (stScores.contains(word)) {
            return stScores.get(word);
        }
        return 0;
    }

    /**
     * @param args
     */
    public static void main(String[] args) {
        In in = new In(args[0]);
        String[] dictionary = in.readAllStrings();
        BoggleSolver solver = new BoggleSolver(dictionary);
        BoggleBoard board = new BoggleBoard(args[1]);
        int score = 0;
        for (String word : solver.getAllValidWords(board)) {
            StdOut.println(word);
            score += solver.scoreOf(word);
        }
        StdOut.println("Score = " + score);
    }
}
