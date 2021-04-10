import edu.princeton.cs.algs4.In;
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.MinPQ;
import edu.princeton.cs.algs4.Stack;
import java.util.Iterator;

public class Solver {
    private SearchNode searchNode;
    private boolean isSolvable;

    // find a solution to the initial board (using the A* algorithm)
    public Solver(Board initial) {
        if (initial == null) throw new IllegalArgumentException();

        MinPQ<SearchNode> mainPQ = new MinPQ<>();
        MinPQ<SearchNode> twinPQ = new MinPQ<>();
        mainPQ.insert(new SearchNode(initial, 0, null));
        twinPQ.insert(new SearchNode(initial.twin(), 0, null));

        searchNode = mainPQ.delMin();
        SearchNode searchNodeOfTwin = twinPQ.delMin();

        isSolvable = searchNode.board.isGoal();
        while (!isSolvable) {
            if (searchNodeOfTwin.board.isGoal()) break;

            for (Board nb : searchNode.board.neighbors()) {
                // Critical optimization.
                if (searchNode.prevSearchNode == null ||
                        !searchNode.prevSearchNode.board.equals(nb)) {
                    mainPQ.insert(new SearchNode(nb, searchNode.moves + 1,
                                searchNode));
                }
            }
            searchNode = mainPQ.delMin();

            for (Board nb : searchNodeOfTwin.board.neighbors()) {
                // Critical optimization.
                if (searchNodeOfTwin.prevSearchNode == null ||
                        !searchNodeOfTwin.prevSearchNode.board.equals(nb)) {
                    twinPQ.insert(new SearchNode(nb, searchNodeOfTwin.moves + 1,
                            searchNodeOfTwin));
                }
            }
            searchNodeOfTwin = twinPQ.delMin();
            isSolvable = searchNode.board.isGoal();
        }

        if (!isSolvable) searchNode = null;
    }

    // is the initial board solvable? (see below)
    public boolean isSolvable() {
        return isSolvable;
    }

    // min number of moves to solve initial board
    public int moves() {
        if (!isSolvable) return -1;
        return searchNode.moves;
    }

    // sequence of boards in a shortest solution
    public Iterable<Board> solution() {
        if (!isSolvable) return null;
        return new Iterable<>() {
            private final Stack<Board> sSolution;
            {
                sSolution = new Stack<>();
                for (SearchNode sn = searchNode; sn != null; sn = sn.prevSearchNode) {
                    sSolution.push(sn.board);
                }
            }
            @Override
            public Iterator<Board> iterator() {
                return sSolution.iterator();
            }
        };
    }

    private static class SearchNode implements Comparable<SearchNode> {
        private final Board board;
        private final int moves;
        private final SearchNode prevSearchNode;
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