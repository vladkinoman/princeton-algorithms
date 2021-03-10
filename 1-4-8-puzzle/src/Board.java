import java.lang.Math;
import java.util.*;

public class Board {
    private Map<PairOfIndices, Integer> board;
    private final Map<PairOfIndices, Integer> goalBoard;
    private final Map<Integer, PairOfIndices> reversedGoalBoard;
    private int n;

    // create a board from an n-by-n array of tiles,
    // where tiles[row][col] = tile at (row, col)
    public Board(int[][] tiles) {
        n = tiles.length;
        board = new LinkedHashMap<>(n*n);
        goalBoard = new LinkedHashMap<>(n*n);
        reversedGoalBoard = new HashMap<>(n*n);
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                board.put(new PairOfIndices(i, j), tiles[i][j]);
                int defaultValue = j + i*n + 1;
                if (i == n - 1 && j == n - 1) defaultValue = 0;
                goalBoard.put(new PairOfIndices(i, j), defaultValue);
                reversedGoalBoard.put(defaultValue, new PairOfIndices(i, j));
            }
        }
    }

    // string representation of this board
    public String toString() {
        Iterator<Integer> it = board.values().iterator();
        String resultS = n + "\n";
        for (int i = 0; i < n; i++) {
            resultS += " ";
            for (int j = 0; j < n; j++) {
                resultS += it.next() + " ";
                if (i != n - 1 && j == n - 1) resultS += "\n";
            }
        }
        return resultS;
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
                    sumOfDist += Math.abs(pIndicesOfBoard.getX() -
                            pIndicesOfReversedGoalBoard.getX()) +
                            Math.abs(pIndicesOfBoard.getY() -
                                    pIndicesOfReversedGoalBoard.getY());
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
    }

    private class PairOfIndices {
        private int x;
        private int y;
        public PairOfIndices(int x, int y) {
            this.x = x;
            this.y = y;
        }

        public int getX() {
            return x;
        }

        public int getY() {
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
}


