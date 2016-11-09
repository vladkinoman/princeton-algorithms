import edu.princeton.cs.algs4.StdRandom;
import edu.princeton.cs.algs4.StdStats;
import edu.princeton.cs.algs4.WeightedQuickUnionUF;

public class PercolationStats {
    private int n;
    private int trials;
    private double xMean;
    private double stddevValue;
    private double confLowValue;
    private double confHighValue;

    // perform trials independent experiments on an n-by-n grid
    public PercolationStats(int n, int trials) {
        if (n <= 0 || trials <= 0) {
            throw new java.lang.IllegalArgumentException("Input correct args.");
        }
        this.n = n;
        this.trials = trials;

        int posX = 0;
        int posY = 0;
        double[] openSites = new double[trials];
        int osCount = 0;
        for (int i = 0; i < trials; i++, osCount = 0) {
            Percolation pObj = new Percolation(n);
            while (!pObj.percolates()) {
                posX = StdRandom.uniform(1, n + 1);
                posY = StdRandom.uniform(1, n + 1);
                if (!pObj.isOpen(posX, posY)) {
                    pObj.open(posX, posY);
                    osCount++;
                }
            }
            openSites[i] = (double) (osCount ) / (n * n);
            xMean += openSites[i];
        }

        xMean /= (double)trials;
        for (int i = 0; i < trials; i++) {
            stddevValue += (openSites[i] - xMean) * (openSites[i] - xMean);
        }
        stddevValue /= (double)trials - 1.0;
        confLowValue = xMean - ((1.96 * Math.sqrt(stddevValue))
                / Math.sqrt(trials));
        confHighValue = xMean + ((1.96 * Math.sqrt(stddevValue))
                / Math.sqrt(trials));
    }

    // sample mean of percolation threshold
    public double mean(){
        return xMean;
    }

    // sample standard deviation of percolation threshold
    public double stddev() {
        return stddevValue;
    }

    // low  endpoint of 95% confidence interval
    public double confidenceLo(){
        return confLowValue;
    }

    // high endpoint of 95% confidence interval
    public double confidenceHi(){
        return confHighValue;
    }

    // test client (described below)
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        int T = Integer.parseInt(args[1]);
        PercolationStats psObj = new PercolationStats(n, T);
        System.out.println("mean = " + psObj.mean());
        System.out.println("stddev = " + psObj.stddev());
        System.out.print("95% confidence interval = " + psObj.confidenceLo() +
        ", " + psObj.confHighValue);
    }
}
