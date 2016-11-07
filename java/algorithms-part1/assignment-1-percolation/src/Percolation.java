/*----------------------------------------------------------------
 *  Author:        Vlad Beklenyshchev
 *  Written:       06/11/2016
 *  Last updated:  07/11/2016
 *
 *  Compilation:   javac Percolation.java
 *  Execution:     java Percolation
 *
 *  Used to know is system percolates or it isn't.
 *
 *  Created in IntelliJ IDEA
 *
 *----------------------------------------------------------------*/

import edu.princeton.cs.algs4.*;

public class Percolation {
    // Grid stores open / blocked state for sites
    private boolean[][] grid;

    // Assists grid to store info about connected sites
    // And to do union and find operations on sites
    private WeightedQuickUnionUF structure;

    // Row (or column) size of matrix
    private int n;

    /**
     * Constructor creates n-by-n grid, with all sites blocked.
     * Also initialize WeightedQuickUnionUF structure.
     *
     * @param n length of row for UF structure. Summary size is n * n + 1
     *          (exclude 0)
     */
    public Percolation(int n) {
        this.n = n; // set given value n to this object n value

        if (n <= 0) {
            throw new java.lang.IllegalArgumentException("n must be " +
                    "greater than 0");
        }

        /*-----------------------------------------------------------------
         *  Create object for UnionFind structure with +1 element to avoid n
         *  in the beginning
         *-----------------------------------------------------------------*/
        structure = new WeightedQuickUnionUF(n * n + 1);

        /*-----------------------------------------------------------------
         * Create grid with +1 row and +1 col - to avoid 0 row and 0 col in the
         * UF structure
         * Also set false automatically (Not necessary to initialize)
         *-----------------------------------------------------------------*/
        grid = new boolean[n + 1][n + 1];
    }

    //

    /**
     * Open current site (row, col) if it is not open already.
     *
     * @param row row index of the current element (first)
     * @param col column index the of current element (second)
     */
    public void open(int row, int col) {
        if (row < 1 || col < 1 || row > n || col > n) {
            throw new java.lang.IndexOutOfBoundsException("Each of the " +
                    "argument values must be greater than or equal to 1" +
                    "and must be less than or equal to n.");
        }

        if (!grid[row][col]) {
            grid[row][col] = true;
        }

        // check the north neighbor and union with it if it is open and there
        // is no connection between them
        if (row >= 2 && row <= n && isOpen(row - 1, col)
                && !structure.connected(n * (row - 1) + col, n * (row - 2)
                + col)) {
            structure.union(n * (row - 1) + col, n * (row - 2) + col);
        }

        // check the earth neighbor and union with it if it is open and there
        // is no connection between them
        if (col >= 1 && col <= n - 1 && isOpen(row, col + 1)
                && !structure.connected(n * (row - 1) + col, n * (row - 1)
                + col + 1)) {
            structure.union(n * (row - 1) + col, n * (row - 1) + col + 1);
        }

        // check the south neighbor and union with it if it is open and there
        // is no connection between them
        if (row >= 1 && row <= n - 1 && isOpen(row + 1, col)
                && !structure.connected(n * (row - 1) + col, n * row + col)) {
            structure.union(n * (row - 1) + col, n * row + col);
        }

        // check the west neighbor and union with it if it is open and there
        // is no connection between them
        if (col >= 2 && col <= n && isOpen(row, col - 1)
                && !structure.connected(n * (row - 1) + col, n * (row - 1)
                + col - 1)) {
            structure.union(n * (row - 1) + col, n * (row - 1) + col - 1);
        }
    }

    /**
     *  Allow to know is current site open.
     *
     * @param row  row index of the current element (first)
     * @param col  column index of the current element (second)
     * @return     true if site is open and return false otherwise
     */
    public boolean isOpen(int row, int col) {
        if (row < 1 || col < 1 || row > n || col > n) {
            throw new java.lang.IndexOutOfBoundsException("Each of the " +
                    "argument values must be greater than or equal to 1" +
                    "and must be less than or equal to n.");
        }

        return grid[row][col];
    }

    /**
     * Check whether there is a path to the current element from the top row.
     *
     * @param row  row index of the current element (first)
     * @param col  column index of the current element (second)
     * @return     true if site is full and return false otherwise
     */
    public boolean isFull(int row, int col) {
        if (row < 1 || col < 1 || row > n || col > n) {
            throw new java.lang.IndexOutOfBoundsException("Each of the " +
                    "argument values must be greater than or equal to 1" +
                    "and must be less than or equal to n.");
        }

        for (int j = 1; j <= n; j++) {
            if (isOpen(1, j) && structure.connected(j, n * (row - 1) + col)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Check does the system percolate.
     *
     * @return  true if system percolates and return false otherwise
     */
    public boolean percolates() {
        for (int i = 1; i <= n; i++) {
            if (isFull(n, i)) {
                return true;
            }
        }
        return false;
    }

    /**
     * It is test client method.
     * Also it is optional for current task.
     *
     * @param args  arguments from command prompt
     */
    public static void main(String[] args) {
        int N = StdIn.readInt();
        Percolation per = new Percolation(N);
        while (!StdIn.isEmpty()) {
            int p = StdIn.readInt();
            int q = StdIn.readInt();
            per.open(p, q);
        }
        System.out.println(per.percolates());
    }
}