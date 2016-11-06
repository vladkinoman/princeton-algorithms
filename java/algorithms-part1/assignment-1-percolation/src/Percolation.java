import edu.princeton.cs.algs4.*;

public class Percolation {
    private WeightedQuickUnionUF structure;
    private boolean [][] grid;
    private int n;
    // create n-by-n grid, with all sites blocked
    public Percolation(int n){
        this.n = n;

        if(n<=0) {
            throw new java.lang.IllegalArgumentException("n must be greater than 0");
        }

        structure = new WeightedQuickUnionUF(n*n);

        // set false automatically
        grid = new boolean[n][n];
    }

    // open site (row, col) if it is not open already
    public void open(int row, int col){
        if(!grid[row][col]) {
            grid[row][col] = true;
        }

        // the north
        if(row >= 1 && row <= n-1 && grid[row-1][col]
                && !structure.connected(n * row + col, n * (row - 1) + col)){
            structure.union(n * row + col, n * (row - 1) + col);
        }

        // the earth
        if(col >= 0 && col <= n-2 && grid[row][col+1]
                && !structure.connected(n * row + col, n * row + col + 1)){
            structure.union(n * row + col, n * row + col + 1);
        }

        // the south
        if(row >= 0 && row <= n-2 && grid[row+1][col]
                && !structure.connected(n * row + col, n * (row+1) + col)){
            structure.union(n * row + col, n * (row+1) + col);
        }

        // the west
        if(col >= 1 && col <= n-1 && grid[row][col-1]
                && !structure.connected(n * row + col, n * row + col - 1)){
            structure.union(n * row + col, n * row + col - 1);
        }
    }

    // is site (row, col) open? 1
    public boolean isOpen(int row, int col){
        return grid[row][col];
    }

    // is site (row, col) full? N + (something) time?
    public boolean isFull(int row, int col){
        for (int i = 0; i < n; i++) {
            if (isOpen(0, i) && structure.connected(n * row + col, i)){
                return true;
            }
        }
        return false;
    }

    // does the system percolate?
    public boolean percolates(){
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (isOpen(0, i) && isOpen(0, j) &&
                        structure.connected(i, n * (n-1) + j)){
                    return true;
                }
            }
        }
        return false;
    }

    // test client (optional)
    public static void main(String[] args){
        int N = StdIn.readInt();
        Percolation per = new Percolation(N);
        while (!StdIn.isEmpty())
        {
            int p = StdIn.readInt();
            int q = StdIn.readInt();
            per.open(p, q);
            //StdOut.println(p + " " + q);
        }
        System.out.println(per.percolates());

        /*Percolation pObj = new Percolation(3);
        pObj.open(1, 1);
        pObj.open(0, 1);
        pObj.open(2, 1);
        System.out.println(pObj.isFull(2, 1));
        System.out.println(pObj.percolates());*/
    }
}
