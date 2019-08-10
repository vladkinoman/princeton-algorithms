import edu.princeton.cs.algs4.WeightedQuickUnionUF;

public class Percolation {
    boolean grid[][];
    int n;
    int openSites;
    WeightedQuickUnionUF ufDataStructure;
    int virtualTopSite;
    int virtualBottomSite;
    WeightedQuickUnionUF ufDataStructureWithTwoExtraSites;

    // creates n-by-n grid, with all sites initially blocked
    public Percolation(int n){
        if (n <= 0)
            throw new IllegalArgumentException();

        virtualTopSite = n * n;
        virtualBottomSite = n * n + 1;
        // using wqu version with 2 additional virtual sites
        ufDataStructure = new WeightedQuickUnionUF( n * n);
        ufDataStructureWithTwoExtraSites = new WeightedQuickUnionUF(n * n + 2);
        grid = new boolean[n][];
        this.n = n;
        for (int i = 0; i < n; i++) {
                grid[i] = new boolean[n];
                for (int j = 0; j < n; j++)
                    grid[i][j] = false;
        }

        // connect top row to the virtual top site
        for (int i = 0; i < n; i++)
            ufDataStructureWithTwoExtraSites.union(i, virtualTopSite);

        // connect bottom row to the virtual bottom site
        for (int i = 0; i < n; i++)
            ufDataStructureWithTwoExtraSites.union(n * (n - 1) + i, virtualBottomSite);

    }

    // opens the site (row, col) if it is not open already
    public void open(int row, int col){
        // elements are counted from 1 to n.
        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if(shiftedRow < 0 || shiftedRow >= n
          || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        if(!grid[shiftedRow][shiftedCol])
        {
            grid[shiftedRow][shiftedCol] = true;

            int curr = shiftedRow * n + shiftedCol;
            int right = shiftedRow * n + shiftedCol + 1;
            int up = (shiftedRow - 1) * n + shiftedCol;
            int left = shiftedRow * n + shiftedCol - 1;
            int bottom = (shiftedRow + 1) * n + shiftedCol;

            if(shiftedCol + 1 < n && grid[shiftedRow][shiftedCol + 1]) {
                ufDataStructure.union(curr, right);
                ufDataStructureWithTwoExtraSites.union(curr, right);
            }

            if(shiftedRow - 1 >= 0 && grid[shiftedRow - 1][shiftedCol]) {
                ufDataStructure.union(curr, up);
                ufDataStructureWithTwoExtraSites.union(curr, up);
            }

            if(shiftedCol - 1 >= 0 && grid[shiftedRow][shiftedCol - 1]) {
                ufDataStructure.union(curr, left);
                ufDataStructureWithTwoExtraSites.union(curr, left);
            }

            if(shiftedRow + 1 < n && grid[shiftedRow + 1][shiftedCol]) {
                ufDataStructure.union(curr, bottom);
                ufDataStructureWithTwoExtraSites.union(curr, bottom);
            }

            openSites++;
        }

    }

    // is the site (row, col) open?
    public boolean isOpen(int row, int col){
        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if(shiftedRow < 0 || shiftedRow >= n
                || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        return grid[shiftedRow][shiftedCol];
    }

    // is the site (row, col) full?
    public boolean isFull(int row, int col){
        if (isOpen(row, col))
            for (int i = 0; i < n; i++)
                if(ufDataStructure.connected((row - 1) * n + (col - 1), i))
                    return true;
        return false;
    }

    // returns the number of open sites
    public int numberOfOpenSites(){ return openSites; }

    // does the system percolate?
    public boolean percolates(){
        return n != 1 ? ufDataStructureWithTwoExtraSites.connected(virtualTopSite, virtualBottomSite) : grid[0][0];
    }

    // test client (optional)
    public static void main(String[] args){
        Percolation newSystem = new Percolation(1);
        System.out.println(newSystem.percolates());
    }
}
