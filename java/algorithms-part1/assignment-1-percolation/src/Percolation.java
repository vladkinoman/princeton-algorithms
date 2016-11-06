import edu.princeton.cs.algs4.*;

public class Percolation {
    private WeightedQuickUnionUF structure;
    private boolean [][] grid;
    private int n;
    // create n-by-n grid, with all sites blocked
    public Percolation(int n){
        this.n = n;

        if(n <= 0) {
            throw new java.lang.IllegalArgumentException("n must be greater than 0");
        }

        structure = new WeightedQuickUnionUF(n*n + 1);

        // set false automatically
        grid = new boolean[n+1][n+1];
    }

    // open site (row, col) if it is not open already
    public void open(int row, int col){
        if(!grid[row][col]) {
            grid[row][col] = true;
        }

        // the north
        if(row >= 2 && row <= n && isOpen(row-1, col)
                && !structure.connected(n * (row-1) + col, n * (row-2) + col)){
            structure.union(n * (row-1) + col, n * (row-2) + col);
        }

        // the earth
        if(col >= 1 && col <= n-1 && isOpen(row, col+1)
                && !structure.connected(n * (row-1) + col, n * (row-1) + col + 1)){
            structure.union(n * (row-1) + col, n * (row-1) + col + 1);
        }

        // the south
        if(row >= 1 && row <= n-1 && isOpen(row+1, col)
                && !structure.connected(n * (row-1) + col, n * row + col)){
            structure.union(n * (row-1) + col, n * row + col);
        }

        // the west
        if(col >= 2 && col <= n && isOpen(row, col-1)
                && !structure.connected(n * (row-1) + col, n * (row-1) + col - 1)){
            structure.union(n * (row-1) + col, n * (row-1) + col - 1);
        }
    }

    // is site (row, col) open? 1
    public boolean isOpen(int row, int col){
        return grid[row][col];
    }

    // is site (row, col) full? N + (something) time?
    public boolean isFull(int row, int col){
        for (int j = 1; j <= n; j++) {
            if (isOpen(1, j) && structure.connected(j, n * (row-1) + col)){
                return true;
            }
        }
        return false;
    }

    // does the system percolate?
    public boolean percolates(){
        for (int i = 1; i <= n; i++) {
            if(isFull(n, i)){
                return true;
            }
        }
        return false;
    }

    // test client (optional)
    public static void main(String[] args){
        int N = StdIn.readInt();
        Percolation per = new Percolation(N);
        int x = 1;
        while (!StdIn.isEmpty())
        {
            int p = StdIn.readInt();
            int q = StdIn.readInt();
            per.open(p, q);
            //StdOut.println(p + " " + q);
            x++;
            if(x == 1413) break;
        }
        System.out.println(per.percolates());
    }
}