import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.MinPQ;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.Queue;

public class Solver {

    private MinPQ<SearchNode> mainPQ;
    private Queue<Board> deletions;
    private int minNumOfMoves;

    // find a solution to the initial board (using the A* algorithm)
    public Solver(Board initial) {
        if (initial == null) throw new IllegalArgumentException();
        mainPQ = new MinPQ<>();
        deletions = new Queue<>();
        mainPQ.insert(new SearchNode(initial, 0, null));
        SearchNode curNode = mainPQ.delMin();
        deletions.enqueue(curNode.board);
        while (!curNode.board.isGoal()) {
            for (Board nb : curNode.board.neighbors()) {
                mainPQ.insert(new SearchNode(nb, curNode.moves + 1, curNode));
            }
            curNode = mainPQ.delMin();
            deletions.enqueue(curNode.board);
        }
        minNumOfMoves = curNode.moves;
    }

    // is the initial board solvable? (see below)
    public boolean isSolvable() {
        return true;
    }

    // min number of moves to solve initial board
    public int moves() {
        if (!isSolvable()) return -1;
        return minNumOfMoves;
    }

    // sequence of boards in a shortest solution
    public Iterable<Board> solution() {
        if (!isSolvable()) return null;
        return deletions;
    }

    private class SearchNode implements Comparable {
        Board board;
        int moves;
        SearchNode prevSearchNode;
        public SearchNode(Board board, int moves, SearchNode prevSearchNode) {
            this.board = board;
            this.moves = moves;
            this.prevSearchNode = prevSearchNode;
        }

        @Override
        public int compareTo(Object o) {
            SearchNode that = (SearchNode)o;
            return this.board.manhattan() + this.moves
                    - (that.board.manhattan() + that.moves);
        }
    }

    // test client
    public static void main(String[] args) {
        // create initial board from file
        In in = new In(args[0]);
        int n = in.readInt();
        int[][] tiles = new int[n][n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                tiles[i][j] = in.readInt();
        Board initial = new Board(tiles);

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