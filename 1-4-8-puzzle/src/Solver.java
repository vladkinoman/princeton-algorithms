import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.MinPQ;
import edu.princeton.cs.algs4.Queue;

public class Solver {

    private final Queue<Board> deletions;
    private final int minNumOfMoves;
    private boolean isSolvable;

    // find a solution to the initial board (using the A* algorithm)
    public Solver(Board initial) {
        if (initial == null) throw new IllegalArgumentException();

        isSolvable = false;
        MinPQ<SearchNode> mainPQ = new MinPQ<>();
        deletions = new Queue<>();
        MinPQ<SearchNode> twinPQ = new MinPQ<>();

        mainPQ.insert(new SearchNode(initial, 0, null));
        twinPQ.insert(new SearchNode(initial.twin(), 0, null));

        SearchNode curSearchNode = mainPQ.delMin();
        SearchNode curSearchNodeOfTwin = twinPQ.delMin();

        deletions.enqueue(curSearchNode.board);

        while (!(isSolvable = curSearchNode.board.isGoal())) {
            if (curSearchNodeOfTwin.board.isGoal()) break;

            for (Board nb : curSearchNode.board.neighbors()) {
                // Critical optimization.
                if (curSearchNode.prevSearchNode == null ||
                        !curSearchNode.prevSearchNode.board.equals(nb)) {
                    mainPQ.insert(new SearchNode(nb, curSearchNode.moves + 1,
                                curSearchNode));
                }
            }
            curSearchNode = mainPQ.delMin();
            deletions.enqueue(curSearchNode.board);

            if (!isSolvable) {
                for (Board nb : curSearchNodeOfTwin.board.neighbors()) {
                    // Critical optimization.
                    if (curSearchNodeOfTwin.prevSearchNode == null ||
                            !curSearchNodeOfTwin.prevSearchNode.board.equals(nb)) {
                        twinPQ.insert(new SearchNode(nb, curSearchNodeOfTwin.moves + 1,
                                curSearchNodeOfTwin));
                    }
                }
                curSearchNodeOfTwin = twinPQ.delMin();
            }
        }
        minNumOfMoves = curSearchNode.moves;
    }

    // is the initial board solvable? (see below)
    public boolean isSolvable() {
        return isSolvable;
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

    private static class SearchNode implements Comparable<SearchNode> {
        Board board;
        int moves;
        SearchNode prevSearchNode;
        private final int cachedDistance;
        public SearchNode(Board board, int moves, SearchNode prevSearchNode) {
            this.board = board;
            this.moves = moves;
            this.prevSearchNode = prevSearchNode;
            // Caching the Hamming and Manhattan priorities
            this.cachedDistance = board.manhattan();
        }

        @Override
        public int compareTo(SearchNode that) {
            return this.cachedDistance + this.moves
                    - (that.cachedDistance + that.moves);
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