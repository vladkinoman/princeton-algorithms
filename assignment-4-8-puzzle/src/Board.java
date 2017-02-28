import edu.princeton.cs.algs4.*;
/**
 * Created by vbekl_000 on 12/26/2016.
 */
public final class Board {
    private final int [][] blocks;
    private final int n;

    // construct a board from an n-by-n array of blocks
    // (where blocks[i][j] = block in row i, column j)
    public Board(int[][] blocks) {
        this.blocks = blocks;
        n = blocks.length;
    }
    // board dimension n
    public int dimension() {
        return n;
    }

    // number of blocks out of place
    public int hamming() {
        int count = 0;
        for (int i = 0; i < dimension(); i++)
            for (int j = 0; j < dimension(); j++)
                if (blocks[i][j] != (dimension() * i + j)
                        || !(i == dimension() - 1 &&
                        j == dimension() - 1 &&
                        blocks[i][j] == 0))
                {
                    count++;
                }
        return count;
    }

    // sum of Manhattan distances between blocks and goal
    public int manhattan() {
        int sum = 0;
        for (int i = 0; i < dimension(); i++)
            for (int j = 0; j < dimension(); j++) {
                if (blocks[i][j] == 0) continue;
                if (blocks[i][j] != (dimension() * i + j)) {
                    sum += calcManhattanDistance(i, j, (blocks[i][j] - 1) / n,
                            (blocks[i][j] - 1) % n);
                }
            }
        return sum;
    }

    private int calcManhattanDistance(int p1, int q1, int p2, int q2) {
        return abs(p1 - p2) + abs(q1 - q2);
    }

    private int abs(int x) {
        if (x < 0) {
            return -x;
        } else {
            return x;
        }
    }

    // is this board the goal board?
    public boolean isGoal() {
        for (int i = 0; i < dimension(); i++)
            for (int j = 0; j < dimension(); j++)
            {
                if (blocks[i][j] != (dimension() * i + j)
                        || !(i == dimension() - 1 &&
                        j == dimension() - 1 &&
                        blocks[i][j] == 0))
                    return false;
            }

        return true;
    }

    // a board that is obtained by exchanging any pair of blocks
    public Board twin() {

    }

    // does this board equal y?
    public boolean equals(Object y) {

    }
    // all neighboring boards
    public Iterable<Board> neighbors() {

    }

    // string representation of this board (in the output format specified below)
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append(n + "\n");
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                s.append(String.format("%2d ", blocks[i][j]));
            }
            s.append("\n");
        }
        return s.toString();
    }

    public static void main(String[] args) {
        // create initial board from file
        In in = new In(args[0]);
        int n = in.readInt();
        int[][] blocks = new int[n][n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                blocks[i][j] = in.readInt();
        Board initial = new Board(blocks);

        // solve the puzzle
        Solver solver = new Solver(initial);

        // print solution to standard output
        if (!solver.isSolvable())
            StdOut.println("No solution possible");
        else {
            StdOut.println("Minimum number of moves = " + solver.moves());
            for (Board board : solver.solution())
                StdOut.println(board);
        }
    }
}
