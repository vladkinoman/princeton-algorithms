import edu.princeton.cs.algs4.StdRandom;

public class PercolationStats {
    private int experimentsCount;
    private int trialsCount;
    private double xMean;
    private double stddevValue;
    private double confLowValue;
    private double confHighValue;

    // perform trials independent experiments on an n-by-n grid
    public PercolationStats(int n, int t) {
        if (n <= 0 || t <= 0) {
            throw new java.lang.IllegalArgumentException("Input correct args.");
        }
        experimentsCount = n;
        trialsCount = t;

        int posX = 0;
        int posY = 0;
        double[] openSites = new double[trialsCount];
        int osCount = 0;
        for (int i = 0; i < trialsCount; i++, osCount = 0) {
            Percolation pObj = new Percolation(experimentsCount);
            while (!pObj.percolates()) {
                posX = StdRandom.uniform(1, experimentsCount + 1);
                posY = StdRandom.uniform(1, experimentsCount + 1);
                if (!pObj.isOpen(posX, posY)) {
                    pObj.open(posX, posY);
                    osCount++;
                }
            }
            openSites[i] = (double) (osCount) / (experimentsCount
                    * experimentsCount);
            xMean += openSites[i];
        }

        xMean /= (double) trialsCount;
        for (int i = 0; i < trialsCount; i++) {
            stddevValue += (openSites[i] - xMean) * (openSites[i] - xMean);
        }
        stddevValue /= (double) trialsCount - 1.0;
        confLowValue = xMean - ((1.96 * Math.sqrt(stddevValue))
                / Math.sqrt(trialsCount));
        confHighValue = xMean + ((1.96 * Math.sqrt(stddevValue))
                / Math.sqrt(trialsCount));
    }

    // sample mean of percolation threshold
    public double mean() {
        return xMean;
    }

    // sample standard deviation of percolation threshold
    public double stddev() {
        return stddevValue;
    }

    // low  endpoint of 95% confidence interval
    public double confidenceLo() {
        return confLowValue;
    }

    // high endpoint of 95% confidence interval
    public double confidenceHi() {
        return confHighValue;
    }

    // test client (described below)
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        int t = Integer.parseInt(args[1]);
        PercolationStats psObj = new PercolationStats(n, t);
        System.out.println("mean = " + psObj.mean());
        System.out.println("stddev = " + psObj.stddev());
        System.out.print("95% confidence interval = " + psObj.confidenceLo() +
        ", " + psObj.confHighValue);
    }
}
