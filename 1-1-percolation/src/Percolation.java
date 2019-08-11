
import edu.princeton.cs.algs4.WeightedQuickUnionUF;

/**
 * The {@code PercolationStats} class provides methods
 * for creating percolation system with two WeightedQuickUnion Data Structures
 * which track opened blocks, add them to components,
 * check whether block is full or system percolates.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class Percolation {
    private boolean grid[][];
    private int n;
    private int openSites;
    private WeightedQuickUnionUF ufDataStructure;
    private int virtualTopSite;
    private int virtualBottomSite;
    private WeightedQuickUnionUF ufDataStructureWithTwoExtraSites;

    /**
     * Creates n-by-n grid, with all sites initially blocked.
     * Performance: time proportional to  4n =  2n + 2n.
     *
     * @param n width of the grid
     */
    public Percolation(int n) {
        if (n <= 0)
            throw new IllegalArgumentException();
        this.n = n;
        grid = new boolean[n][n];
        virtualTopSite = n * n;
        virtualBottomSite = n * n + 1;

        // using wqu version with 2 additional virtual sites
        ufDataStructure = new WeightedQuickUnionUF(n * n); // n
        ufDataStructureWithTwoExtraSites =
                new WeightedQuickUnionUF(n * n + 2);       // n

        // connect top row to the virtual top site
        for (int i = 0; i < n; i++)                           // n
            ufDataStructureWithTwoExtraSites.union(i, virtualTopSite);

        // connect bottom row to the virtual bottom site
        for (int i = 0; i < n; i++)                          // n
            ufDataStructureWithTwoExtraSites.union(n * (n - 1) + i,
                    virtualBottomSite);
    }

    /**
     * Opens the site (row, col) if it is not open already.
     * Performance: constant time plus a constant number of calls to the uf method union()
     * We have 2 * 4 = 8 calls to the union() method in the worst case.
     * Notice that row and col are counted from 1 to n.
     *
     * @param row row number of the element
     * @param col column number of the element
     */
    public void open(int row, int col) {

        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if (shiftedRow < 0 || shiftedRow >= n
                || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        if (!grid[shiftedRow][shiftedCol]) {

            grid[shiftedRow][shiftedCol] = true;

            int curr = shiftedRow * n + shiftedCol;
            int right = shiftedRow * n + shiftedCol + 1;
            int up = (shiftedRow - 1) * n + shiftedCol;
            int left = shiftedRow * n + shiftedCol - 1;
            int bottom = (shiftedRow + 1) * n + shiftedCol;

            if (shiftedCol + 1 < n && grid[shiftedRow][shiftedCol + 1]) {
                ufDataStructure.union(curr, right);
                ufDataStructureWithTwoExtraSites.union(curr, right);
            }

            if (shiftedRow - 1 >= 0 && grid[shiftedRow - 1][shiftedCol]) {
                ufDataStructure.union(curr, up);
                ufDataStructureWithTwoExtraSites.union(curr, up);
            }

            if (shiftedCol - 1 >= 0 && grid[shiftedRow][shiftedCol - 1]) {
                ufDataStructure.union(curr, left);
                ufDataStructureWithTwoExtraSites.union(curr, left);
            }

            if (shiftedRow + 1 < n && grid[shiftedRow + 1][shiftedCol]) {
                ufDataStructure.union(curr, bottom);
                ufDataStructureWithTwoExtraSites.union(curr, bottom);
            }

            openSites++;
        }
    }

    /**
     * Returns a boolean value which is true when the site (row, col) is open
     * and returns false otherwise.
     * Performance: constant time.
     *
     * @param row row number of the element
     * @param col column number of the element
     * @return {@code true} if the site is full, {@code false} otherwise
     */
    public boolean isOpen(int row, int col) {
        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if (shiftedRow < 0 || shiftedRow >= n
                || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        return grid[shiftedRow][shiftedCol];
    }

    /**
     * Returns a boolean value which is true when the site (row, col) is full
     * (flooded with water / painted blue) and returns false otherwise.
     * Performance: n calls to the uf method connected() in the worst case :/
     *
     * @param row row number of the element
     * @param col column number of the element
     * @return {@code true} if the site is full, {@code false} otherwise
     */
    public boolean isFull(int row, int col) {
        if (isOpen(row, col))
            for (int i = 0; i < n; i++)
                // worst case scenario: when all blocks of the top row are opened
                // and possible connected block is the last one
                if (grid[0][i] && ufDataStructure.connected((row - 1) * n
                        + (col - 1), i))
                    return true;
        return false;
    }

    /**
     * Returns the number of open sites.
     * Performance: constant time.
     *
     * @return an integer value of the number of open sites.
     */
    public int numberOfOpenSites() {
        return openSites;
    }

    /**
     * Returns a boolean value which is true when the system percolates
     * and false otherwise.
     * Performance: only 1 call to the uf method connected().
     *
     * @return {@code true} if the system percolates, {@code false} otherwise
     */
    public boolean percolates() {
        return n != 1 ? ufDataStructureWithTwoExtraSites.connected(
                virtualTopSite, virtualBottomSite) : grid[0][0];
    }

    /**
     * Test client for Percolation.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        Percolation newSystem = new Percolation(1);
        System.out.println(newSystem.percolates());
    }
}
