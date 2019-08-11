
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdRandom;
import edu.princeton.cs.algs4.StdStats;

/**
 * The {@code PercolationStats} class provides methods
 * for computing percolation threshold.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class PercolationStats {
    // see: https://en.wikipedia.org/wiki/1.96
    private static final double PART_OF_STANDARD_DEVIATION = 1.96;
    private final int trials; // trials - number of observations in the experiment
    private final double mean;
    private final double stddev;

    /**
     * Perform independent trials on an n-by-n grid.
     *
     * @param n width of the grid
     * @param trials number of independent trials
     */
    public PercolationStats(int n, int trials) {
        if (n <= 0 || trials <= 0)
            throw new IllegalArgumentException();

        this.trials = trials;
        double[] arrFractionOfOpenSites = new double[trials];
        for (int t = 0; t < trials; t++) {
            Percolation perc = new Percolation(n);
            while (!perc.percolates()) {
                int row = 0;
                int col = 0;
                do {
                    row = StdRandom.uniform(1, n + 1);
                    col = StdRandom.uniform(1, n + 1);
                    // while we don't get a blocked site
                } while (perc.isOpen(row, col));
                perc.open(row, col);
            }
            arrFractionOfOpenSites[t] = (double) perc.numberOfOpenSites()
                    / (n * n);
        }
        mean = StdStats.mean(arrFractionOfOpenSites);
        stddev = StdStats.stddev(arrFractionOfOpenSites);
    }
    
    /**
     * Returns a sample mean of percolation threshold.
     * Provides an estimate of the percolation threshold.
     *
     * @return a sample mean of percolation threshold.
     */
    public double mean() {
        return mean;
    }

    /**
     * Sample standard deviation of percolation threshold.
     * It measures the sharpness of the threshold.
     *
     * @return standard deviation of percolation threshold
     */
    public double stddev() {
        return stddev;
    }

    /**
     * Returns a low endpoint of 95% confidence interval.
     *
     * @return a low endpoint of 95% confidence interval
     */
    public double confidenceLo() {
        return mean() - PART_OF_STANDARD_DEVIATION * stddev()
                / Math.sqrt(trials);
    }

    /**
     * Returns a high endpoint of 95% confidence interval.
     *
     * @return a right value from the confidence interval
     */
    public double confidenceHi() {
        return mean() + PART_OF_STANDARD_DEVIATION * stddev()
                / Math.sqrt(trials);
    }

    /**
     * Test client for PercolationStats.
     *
     * @param args the command-line arguments
     */
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        int trials = Integer.parseInt(args[1]);
        PercolationStats newPercStats = new PercolationStats(n, trials);
        StdOut.println("mean                    = " + newPercStats.mean());
        StdOut.println("stddev                  = " + newPercStats.stddev());
        StdOut.println("95% confidence interval = ["
                + newPercStats.confidenceLo() + ", "
                + newPercStats.confidenceHi() + "]");
    }

}
