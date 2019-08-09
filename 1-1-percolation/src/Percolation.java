import edu.princeton.cs.algs4.WeightedQuickUnionUF;

public class Percolation {
    private boolean grid[][];
    private int n;
    private int openSites;
    WeightedQuickUnionUF ufDataStructure;

    // creates n-by-n grid, with all sites initially blocked
    public Percolation(int n){
        if (n <= 0)
            throw new IllegalArgumentException();

        // using wqu version with 2 additional virtual sites
        ufDataStructure = new WeightedQuickUnionUF(n + 2);

        grid = new boolean[n][];
        this.n = n;
        for (int i = 0; i < n; i++) {
            {
                grid[i] = new boolean[n];
                for (int j = 0; j < n; j++)
                    grid[i][j] = false;
            }
        }

        // connect top row to the virtual top site
        for (int i = 0; i < n; i++)
            ufDataStructure.union(i, n * n);

        // connect bottom row to the virtual bottom site
        for (int i = 0; i < n; i++)
            ufDataStructure.union(n * (n - 1) + i, n * n + 1);

    }

    // opens the site (row, col) if it is not open already
    public void open(int row, int col){
        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if(shiftedRow < 0 || shiftedRow >= n
          || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        if(!grid[shiftedRow][shiftedCol])
        {
            grid[shiftedRow][shiftedCol] = true;

            int curr = row * n + col;
            int right = row * n + col + 1;
            int up = (row - 1) * n + col;
            int left = row * n + col - 1;
            int bottom = (row + 1) * n + col;

            if(shiftedCol + 1 < n && grid[shiftedRow][shiftedCol + 1])
                ufDataStructure.union(curr, right);

            if(shiftedRow - 1 >= 0 && grid[shiftedRow - 1][shiftedCol])
                ufDataStructure.union(curr, up);

            if(shiftedCol - 1 >= 0 && grid[shiftedRow][shiftedCol - 1])
                ufDataStructure.union(curr, left);

            if(shiftedRow + 1 < n && grid[shiftedRow + 1][shiftedCol])
                ufDataStructure.union(curr, bottom);

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
        int shiftedRow = row - 1;
        int shiftedCol = col - 1;

        if(shiftedRow < 0 || shiftedRow >= n
                || shiftedCol < 0 || shiftedCol >= n)
            throw new IllegalArgumentException();

        return !grid[shiftedRow][shiftedCol];
    }

    // returns the number of open sites
    public int numberOfOpenSites(){ return openSites; }

    // does the system percolate?
    public boolean percolates(){
        return n != 1 ? ufDataStructure.connected(n * n, n * n + 1) : grid[0][0];
    }

    // test client (optional)
    public static void main(String[] args){
        Percolation newSystem = new Percolation(1);
        System.out.println(newSystem.percolates());
    }
}
