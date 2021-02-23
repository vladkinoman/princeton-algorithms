import edu.princeton.cs.algs4.MinPQ;
import java.lang.Math;

public class Board {
    private int[] board;
    private final int[] goalBoard;

    // create a board from an n-by-n array of tiles,
    // where tiles[row][col] = tile at (row, col)
    public Board(int[][] tiles) {
        int n = tiles.length;

        board = new int[n*n];
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                board[j + i*n] = tiles[i][j];
            }
        }

        goalBoard = new int[n*n];
        for (int i = 1; i < n*n; i++) {
            goalBoard[i-1] = i;
        }
        goalBoard[n*n] = 0;
    }

    // string representation of this board
    public String toString() {
        int n = this.dimension();
        String resultS = n + "\n";
        for (int i = 0; i < n; i++) {
            resultS += " ";
            for (int j = 0; j < n; j++) {
                 resultS += board[j + i*n] + " ";
            }
            resultS += "\n";
        }
        return resultS;
    }

    // board dimension n
    public int dimension() {
        return board.length/board.length;
    }

    // number of tiles out of place
    public int hamming() {
        int dist = 0;
        int n = this.dimension();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (board[j + i*n] == goalBoard[j + i*n]) dist++;
            }
        }
        return dist;
    }

    // sum of Manhattan distances between tiles and goal
    public int manhattan() {
        int sumOfDist = 0;
        int n = this.dimension();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                sumOfDist += Math.abs(i - ) + Math ( i - )
            }
        }
        return sumOfDist;
    }

    // is this board the goal board?
    public boolean isGoal() {
        return hamming() == 0;
    }

    // does this board equal y?
    public boolean equals(Object y) {
        return false;
    }

    // all neighboring boards
    public Iterable<Board> neighbors() {
        return null;
    }

    // a board that is obtained by exchanging any pair of tiles
    public Board twin() {
        return null;
    }

    // unit testing (not graded)
    public static void main(String[] args) {

    }

}
