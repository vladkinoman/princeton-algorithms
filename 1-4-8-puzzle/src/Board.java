import java.lang.Math;
import java.util.*;

public class Board {
    private final int n;
    private int[][] copyOfTiles;

    private final Map<PairOfIndices, Integer> board;
    private PairOfIndices blank;
    private final Map<PairOfIndices, Integer> goalBoard;
    private final Map<Integer, PairOfIndices> reversedGoalBoard;

    private final List<Board> lNeighbors;

    private class PairOfIndices {
        private final int x;
        private final int y;
        public PairOfIndices(int x, int y) {
            this.x = x;
            this.y = y;
        }

        public int getRow() {
            return x;
        }

        public int getCol() {
            return y;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            PairOfIndices that = (PairOfIndices) o;
            return x == that.x && y == that.y;
        }

        @Override
        public int hashCode() {
            return Objects.hash(x, y);
        }

        @Override
        public String toString() {
            return "PairOfIndices{" +
                    "x=" + x +
                    ", y=" + y +
                    '}';
        }
    }

    // create a board from an n-by-n array of tiles,
    // where tiles[row][col] = tile at (row, col)
    public Board(int[][] tiles) {
        n = tiles.length;
        copyOfTiles = new int[n][];
        for (int i = 0; i < n; i++) {
            copyOfTiles[i] = new int[n];
            for (int j = 0; j < n; j++) {
                copyOfTiles[i][j] = tiles[i][j];
            }
        }

        board = new LinkedHashMap<>(n*n);
        goalBoard = new LinkedHashMap<>(n*n);
        reversedGoalBoard = new HashMap<>(n*n);
        blank = null;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (tiles[i][j] == 0) blank = new PairOfIndices(i, j);
                board.put(new PairOfIndices(i, j), tiles[i][j]);
                int defaultValue = j + i*n + 1;
                if (i == n - 1 && j == n - 1) defaultValue = 0;
                goalBoard.put(new PairOfIndices(i, j), defaultValue);
                reversedGoalBoard.put(defaultValue, new PairOfIndices(i, j));
            }
        }
        lNeighbors = new ArrayList<>();
    }

    // string representation of this board
    public String toString() {
        Iterator<Integer> it = board.values().iterator();
        StringBuilder s = new StringBuilder();
        s.append(n).append("\n");
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                s.append(String.format("%2d ", it.next()));
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
        int dist = 0;
        Iterator<Integer> itBoard = board.values().iterator();
        Iterator<Integer> itGoalBoard = goalBoard.values().iterator();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if ((i != n-1 || j != n-1) && !itBoard.next()
                        .equals(itGoalBoard.next())) {
                    dist++;
                }
            }
        }
        return dist;
    }

    // sum of Manhattan distances between tiles and goal
    public int manhattan() {
        int sumOfDist = 0;
        Iterator<Integer> itValuesOfBoard = board.values().iterator();
        Iterator<PairOfIndices> itIndicesOfBoard = board.keySet().iterator();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                int valOfBoard = itValuesOfBoard.next();
                PairOfIndices pIndicesOfBoard = itIndicesOfBoard.next();
                PairOfIndices pIndicesOfReversedGoalBoard = reversedGoalBoard
                        .get(valOfBoard);
                if (valOfBoard != 0) {
                    sumOfDist += Math.abs(pIndicesOfBoard.getRow() -
                            pIndicesOfReversedGoalBoard.getRow()) +
                            Math.abs(pIndicesOfBoard.getCol() -
                                    pIndicesOfReversedGoalBoard.getCol());
                }
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
        if (this == y) return true;
        if (y == null || getClass() != y.getClass()) return false;
        Board that = (Board) y;
        return this.board.equals(that.board);
    }

    // all neighboring boards
    public Iterable<Board> neighbors() {
        int blankRow = blank.getRow();
        int blankCol = blank.getCol();
        if (blankCol != 0) {
            swap(copyOfTiles, blankRow, blankCol, blankRow, blankCol-1);
            lNeighbors.add(new Board(copyOfTiles));
            swap(copyOfTiles, blankRow, blankCol, blankRow, blankCol-1);
        }
        if (blankRow != 0) {
            swap(copyOfTiles, blankRow, blankCol, blankRow-1, blankCol);
            lNeighbors.add(new Board(copyOfTiles));
            swap(copyOfTiles, blankRow, blankCol, blankRow-1, blankCol);
        }
        if (blankCol != n-1) {
            swap(copyOfTiles, blankRow, blankCol, blankRow, blankCol+1);
            lNeighbors.add(new Board(copyOfTiles));
            swap(copyOfTiles, blankRow, blankCol, blankRow, blankCol+1);
        }
        if (blankRow != n-1) {
            swap(copyOfTiles, blankRow, blankCol, blankRow+1, blankCol);
            lNeighbors.add(new Board(copyOfTiles));
            swap(copyOfTiles, blankRow, blankCol, blankRow+1, blankCol);
        }
        return lNeighbors;
    }

    // a board that is obtained by exchanging any pair of tiles
    public Board twin() {
        int count = 0;
        int p1=0, q1=0, p2=0, q2=0;
        for (int i = 0; i < n && count < 2; i++) {
            for (int j = 0; j < n && count < 2; j++) {
                if (copyOfTiles[i][j] != 0) {
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
        swap(copyOfTiles, p1, q1, p2, q2);
        Board twin = new Board(copyOfTiles);
        swap(copyOfTiles, p1, q1, p2, q2);
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
