import java.lang.Math;
import java.util.List;
import java.util.ArrayList;

public class Board {
    private final int n;
    private final int[][] board;
    private final int[] goalBoard;
    private int blankX;
    private int blankY;
    private final List<Board> lNeighbors = new ArrayList<>();

    // create a board from an n-by-n array of tiles,
    // where tiles[row][col] = tile at (row, col)
    public Board(int[][] tiles) {
        n = tiles.length;
        board = new int[n][];
        goalBoard = new int[n*n];

        for (int i = 0; i < n; i++) {
            board[i] = new int[n];
            for (int j = 0; j < n; j++) {
                if (tiles[i][j] == 0) {
                    blankX = i; blankY = j;
                }
                board[i][j] = tiles[i][j];
                int defaultValue = j + i * n + 1;
                if (i == n - 1 && j == n - 1) defaultValue = 0;
                goalBoard[j + i * n] = defaultValue;
            }
        }
    }

    // string representation of this board
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append(n).append("\n");
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                s.append(String.format("%2d ", board[i][j]));
            }
            s.append("\n");
        }
        return s.toString();
    }

    // board dimension n
    public int dimension() {
        return n;
    }

    // number of tiles out of place
    public int hamming() {
        int distance = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if ((i != n-1 || j != n-1) && board[i][j] != goalBoard[j + i * n]) {
                    distance++;
                }
            }
        }
        return distance;
    }

    // sum of Manhattan distances between tiles and goal
    public int manhattan() {
        int sumOfDistances = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                int p = 0, q = 0;
                for (int k = 0; k < n * n; k++) {
                    if (goalBoard[k] == board[i][j]) {
                        p = k / n; q = k % n;
                        break;
                    }
                }
                if (board[i][j] != 0) {
                    sumOfDistances += Math.abs(p - i) + Math.abs(q - j);
                }
            }
        }

        return sumOfDistances;
    }

    // is this board the goal board?
    public boolean isGoal() {
        return hamming() == 0;
    }

    // does this board equal y?
    public boolean equals(Object y) {
        if (this == y) return true;
        if (y == null || getClass() != y.getClass()) return false;
        Board that = (Board) y;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (this.board[i][j] != that.board[i][j]) {
                    return false;
                }
            }
        }
        return true;
    }

    // all neighboring boards
    public Iterable<Board> neighbors() {
        int blankRow = blankX;
        int blankCol = blankY;
        if (blankCol != 0) {
            swap(board, blankRow, blankCol, blankRow, blankCol-1);
            lNeighbors.add(new Board(board));
            swap(board, blankRow, blankCol, blankRow, blankCol-1);
        }
        if (blankRow != 0) {
            swap(board, blankRow, blankCol, blankRow-1, blankCol);
            lNeighbors.add(new Board(board));
            swap(board, blankRow, blankCol, blankRow-1, blankCol);
        }
        if (blankCol != n-1) {
            swap(board, blankRow, blankCol, blankRow, blankCol+1);
            lNeighbors.add(new Board(board));
            swap(board, blankRow, blankCol, blankRow, blankCol+1);
        }
        if (blankRow != n-1) {
            swap(board, blankRow, blankCol, blankRow+1, blankCol);
            lNeighbors.add(new Board(board));
            swap(board, blankRow, blankCol, blankRow+1, blankCol);
        }
        return lNeighbors;
    }

    // a board that is obtained by exchanging any pair of tiles
    public Board twin() {
        int count = 0;
        int p1=0, q1=0, p2=0, q2=0;
        for (int i = 0; i < n && count < 2; i++) {
            for (int j = 0; j < n && count < 2; j++) {
                if (board[i][j] != 0) {
                    if (count == 0) {
                        p1 = i;
                        q1 = j;
                    } else {
                        p2 = i;
                        q2 = j;
                    }
                    count++;
                }
            }
        }
        swap(board, p1, q1, p2, q2);
        Board twin = new Board(board);
        swap(board, p1, q1, p2, q2);
        return twin;
    }

    // unit testing (not graded)
    public static void main(String[] args) {
        int [][] tiles = new int[][]{
                {8, 1, 3},
                {4, 0, 2},
                {7, 6, 5}
        };
        Board board = new Board(tiles);
        System.out.println("Our board:");
        System.out.println(board);
        System.out.println("Dimension: " + board.dimension());
        System.out.println("Hamming distance: " + board.hamming());
        System.out.println("Manhattan distance: " + board.manhattan());
        System.out.println("Neighbors:");
        for (Board neighborBoard: board.neighbors()) {
            System.out.println(neighborBoard);
        }
        System.out.println("Twin: ");
        System.out.println(board.twin());
        int [][] tiles2 = new int[][]{
                {8, 1, 3},
                {4, 0, 2},
                {7, 6, 5}
        };
        Board boardCopy = new Board(tiles2);
        System.out.println("Are those matrices equal?");
        if (board.equals(boardCopy)) System.out.println("Yes.");
        else                         System.out.println("No.");
    }

    private void swap(int[][] arr, int i, int j, int p, int q) {
        int tmp = arr[i][j];
        arr[i][j] = arr[p][q];
        arr[p][q] = tmp;
    }
}
