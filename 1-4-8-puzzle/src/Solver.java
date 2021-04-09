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
        SearchNode curSearchNode = mainPQ.delMin();
        deletions.enqueue(curSearchNode.board);
        while (!curSearchNode.board.isGoal()) {
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
        }
        minNumOfMoves = curSearchNode.moves;
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
        private int cachedDistance;
        public SearchNode(Board board, int moves, SearchNode prevSearchNode) {
            this.board = board;
            this.moves = moves;
            this.prevSearchNode = prevSearchNode;
            // Caching the Hamming and Manhattan priorities
            this.cachedDistance = board.manhattan();
        }

        @Override
        public int compareTo(Object o) {
            SearchNode that = (SearchNode)o;
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