
import edu.princeton.cs.algs4.StdOut;
import edu.princeton.cs.algs4.StdRandom;

/**
 * The {@code PercolationStats} class provides methods
 * for computing percolation threshold.
 *
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class PercolationStats {
    private int n; // width of the grid
    private int trials; // trials - number of observations in the experiment
    private double sumOfFractionOfOpenSites;
    private double[] arrFractionOfOpenSites;
    // see: https://en.wikipedia.org/wiki/1.96
    private final double partOfStandardDeviation = 1.96;

    /**
     * Perform independent trials on an n-by-n grid.
     *
     * @param n width of the grid
     * @param trials number of independent trials
     */
    public PercolationStats(int n, int trials) {
        if (n <= 0 || trials <= 0)
            throw new IllegalArgumentException();
        this.n = n;
        this.trials = trials;
        arrFractionOfOpenSites = new double[trials];
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
            sumOfFractionOfOpenSites += arrFractionOfOpenSites[t];
        }
    }
    
    /**
     * Returns a sample mean of percolation threshold.
     * Provides an estimate of the percolation threshold.
     *
     * @return a sample mean of percolation threshold.
     */
    public double mean() {
        return sumOfFractionOfOpenSites / trials;
    }

    /**
     * Sample standard deviation of percolation threshold.
     * It measures the sharpness of the threshold.
     *
     * @return standard deviation of percolation threshold
     */
    public double stddev() {
        double sumOfSquares = 0;
        for (int i = 0; i < trials; i++)
            sumOfSquares += (arrFractionOfOpenSites[i]
                - mean()) * (arrFractionOfOpenSites[i] - mean());

        return Math.sqrt(sumOfSquares / (trials - 1));
    }

    /**
     * Returns a low endpoint of 95% confidence interval.
     *
     * @return a low endpoint of 95% confidence interval
     */
    public double confidenceLo() {
        return mean() - partOfStandardDeviation * stddev() / Math.sqrt(trials);
    }

    /**
     * Returns a high endpoint of 95% confidence interval.
     *
     * @return a right value from the confidence interval
     */
    public double confidenceHi() {
        return mean() + partOfStandardDeviation * stddev() / Math.sqrt(trials);
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
