import java.util.Arrays;

import edu.princeton.cs.algs4.Picture;

/**
 * The {@code SeamCarver} represents a data type for resizing an image without
 * distortion for display on cell phones and web browsers.
 * 
 * <p>
 * This implementation runs Kahn's topological sorting algorithm 
 * (see https://www.guru99.com/topological-sort-algorithm.html) from each vertex.
 * The constructor takes time proportional to <em>width</em> × <em>height</em>,
 * where <em>width</em> is the width of a given picture and <em>height</em>
 * is the height of a given picture.
 * Afterwards, the {@code width()}, {@code height()}, {@code energy} methods
 * take constant time. The {@code picture()}, {@code findHorizontalSeam()},
 * {@code findVerticalSeam()}, {@code removeHorizontalSeam()},
 * {@code removeVerticalSeam()} methods take time proportional to 
 * <em>width</em> × <em>height</em>.
 * 
 * @author Vlad Beklenyshchev aka vladkinoman
 */
public class SeamCarver {
    private Picture picture;
    private double[][] aEnergy;
    private boolean isPictureTransposed;
    private boolean isVerticalCalledFromHorizontal;

    /**
     * Create a seam carver object based on the given picture.
     * @param picture given picture
     * @throws IllegalArgumentException unless the argument is not a null
     */
    public SeamCarver(final Picture picture) {
        validateForNull(picture);
        this.picture = new Picture(picture);
        calculateEnergy();
    }

    private void calculateEnergy() {
        int hei = picture.height();
        int wid = picture.width();
        
        int[][] aRGB = new int[hei][];
        for (int i = 0; i < hei; i++) {
            aRGB[i] = new int[wid];
            for (int j = 0; j < wid; j++) {
                aRGB[i][j] = picture.get(j, i).getRGB();
            }
        }
        
        aEnergy = new double[hei][];
        for (int i = 0; i < hei; i++) {
            aEnergy[i] = new double[wid];
            for (int j = 0; j < wid; j++) {
                if (i == 0 || i == hei-1 || j == 0 || j == wid-1) {
                    aEnergy[i][j] = 1000;
                } else {
                    int iRGB = 0;
                    iRGB = aRGB[i-1][j];
                    int iRxLeft = (iRGB >> 16) & 0xFF;
                    int iGxLeft = (iRGB >> 8) & 0xFF;
                    int iBxLeft = (iRGB >> 0) & 0xFF;
                    iRGB = aRGB[i+1][j];
                    int iRxRight = (iRGB >> 16) & 0xFF;
                    int iGxRight = (iRGB >> 8) & 0xFF;
                    int iBxRight = (iRGB >> 0) & 0xFF;

                    iRGB = aRGB[i][j-1];
                    int iRyUp = (iRGB >> 16) & 0xFF;
                    int iGyUp = (iRGB >> 8) & 0xFF;
                    int iByUp = (iRGB >> 0) & 0xFF;
                    iRGB = aRGB[i][j+1];
                    int iRyDown = (iRGB >> 16) & 0xFF;
                    int iGyDown = (iRGB >> 8) & 0xFF;
                    int iByDown = (iRGB >> 0) & 0xFF;

                    aEnergy[i][j] = Math.sqrt(
                        (iRxRight-iRxLeft)*(iRxRight-iRxLeft)
                      + (iGxRight-iGxLeft)*(iGxRight-iGxLeft) 
                      + (iBxRight-iBxLeft)*(iBxRight-iBxLeft)
                      + (iRyDown-iRyUp)*(iRyDown-iRyUp)
                      + (iGyDown-iGyUp)*(iGyDown-iGyUp)
                      + (iByDown-iByUp)*(iByDown-iByUp)
                    );
                }
            }
        }
    }

    private void transpose() {
        int wid = picture.height();
        int hei = picture.width();
        double[][] newAEnergy = new double[hei][];
        Picture newp = new Picture(wid, hei);
        for (int i = 0; i < hei; i++) {
            newAEnergy[i]  = new double[wid];
            for (int j = 0; j < wid; j++) {
                newAEnergy[i][j]  = aEnergy[j][i];
                newp.set(j, i, picture.get(i, j));
            }
        }
        aEnergy = newAEnergy;
        picture = newp;
    }

    private void allPairsSP(double[][] distTo, int[][] vertexTo) {
        int wid = picture.width();
        int hei = picture.height();
        if (hei <= 2 || wid <= 2) {
            // this is the case when each energy equals 1000,
            // b/c we don't have inner part, just border
            // the code will return first row/col, see findVerticalSeam()
            return;
        }
        for (int s = 0; s < wid; s++) {
            distTo[0][s] = 0.0;
            for (int i = 0; i < hei; i++) {
                for (int j = 0; j < wid; j++) {
                    if (i == hei-1) {
                        if (distTo[i][j] != Double.POSITIVE_INFINITY) {
                            distTo[i][j] += aEnergy[i][j];
                        }
                    } else if (j == 0) {
                        relax(distTo, vertexTo, i, j, 0);
                        relax(distTo, vertexTo, i, j, 1);
                    } else if (j == wid-1) {
                        relax(distTo, vertexTo, i, j, -1);
                        relax(distTo, vertexTo, i, j, 0);
                    } else if (i != hei-1) {
                        relax(distTo, vertexTo, i, j, -1);
                        relax(distTo, vertexTo, i, j, 0);
                        relax(distTo, vertexTo, i, j, 1);
                    }      
                }
            }
        }
    }

    private void relax(double[][] distTo, int[][] vertexTo, 
    final int i, final int j, final int k) {
        if (distTo[i+1][j+k] > distTo[i][j] + aEnergy[i][j])
        {
            distTo[i+1][j+k] = distTo[i][j] + aEnergy[i][j];
            vertexTo[i+1][j+k] = j;
        }
    }

    private void validateForNull(final Object obj) {
        if (obj == null) {
            throw new IllegalArgumentException(
                "the argument is null");
        }
    }

    private void validateCoordinate(final int x, final int upperbound) {
        if (x < 0 || x > upperbound - 1) {
            throw new IllegalArgumentException(
                "the coordinate is outside its prescribed range.");
        }
    }

    private void validatePicture() {
        if (picture.width() <= 1) {
            throw new IllegalArgumentException(
                "the width of the picture is less than or equal to 1");
        }
    }

    private void validateSeam(final int[] seam) {
        int wid = picture.width();
        int hei = picture.height();
        if (seam.length != hei) {
            throw new IllegalArgumentException(
                "the array of the wrong length");
        }

        for (int element : seam) {
            if (element < 0 || element > wid-1) {
                throw new IllegalArgumentException(
                    "the seam entry is outside its prescribed range");
            }
        }

        for (int i = 0; i < hei-1; i++) {
            if (Math.abs(seam[i] - seam[i+1]) > 1) {
                throw new IllegalArgumentException(
                    "two adjacent seam entries differ by more than 1");
            }
        }
    }
 
    /**
     * Returns current picture.
     * @return current picture as Picture object
     */
    public Picture picture() {
        if (isPictureTransposed) {
            transpose();
            isPictureTransposed = false;
        }
        return new Picture(picture);
    }
 
    /**
     * Returns width of current picture.
     * @return width of current picture
     */
    public int width() {
        int result = 0;
        if (isPictureTransposed) {
            result = picture.height();
        } else {
            result = picture.width();
        }
        return result;
    }
 
    /**
     * Returns height of current picture.
     * @return height of current picture
     */
    public int height() {
        int result = 0;
        if (isPictureTransposed) {
            result = picture.width();
        } else {
            result = picture.height();
        }
        return result;
    }

    /**
     * Returns energy of pixel at column x and row y.
     * @param x x-coordinate of pixel
     * @param y y-coordinate of pixel
     * @return energy of pixel at column x and row y
     * @throws IllegalArgumentException unless x & y are in the prescribed
     * range
     */
    public double energy(final int x, final int y) {
        double result = 0.0;
        if (isPictureTransposed) {
            validateCoordinate(x, aEnergy.length);
            validateCoordinate(y, aEnergy[0].length);
            result = aEnergy[x][y];
        } else {
            validateCoordinate(x, aEnergy[0].length);
            validateCoordinate(y, aEnergy.length);
            result = aEnergy[y][x];
        }
        return result;
    }
 
    /**
     * Returns sequence of indices for horizontal seam.
     * @return sequence of indices for horizontal seam
     */
    public int[] findHorizontalSeam() {
        if (!isPictureTransposed) {
            transpose();
            isPictureTransposed = true;
        }
        isVerticalCalledFromHorizontal = true;
        int[] result = findVerticalSeam();
        isVerticalCalledFromHorizontal = false;
        return result;
    }

    /**
     * Returns sequence of indices for vertical seam.
     * @return sequence of indices for vertical seam
     */
    public int[] findVerticalSeam() {
        if (isPictureTransposed && !isVerticalCalledFromHorizontal) {
            transpose();
            isPictureTransposed = false;
        }
        int hei = picture.height();
        int wid = picture.width();
        double[][] distTo = new double[hei][];
        int[][] vertexTo = new int[hei][];
        for (int i = 0; i < hei; i++) {
            distTo[i] = new double[wid];
            vertexTo[i] = new int[wid];
            for (int j = 0; j < wid; j++) {
                distTo[i][j] = Double.POSITIVE_INFINITY;
                vertexTo[i][j] = -1;
            }
        }
        allPairsSP(distTo, vertexTo);
        
        int[] seam = new int[hei];
        
        if (hei <= 2 || wid <= 2) {
            // array is initialized explicitly in order to remove the warning
            // it's all we need if we want to remove first col/row
            Arrays.fill(seam, 0);
            return seam;
        }
        int id = -1;
        double minEnergy = Double.POSITIVE_INFINITY;
        for (int i = 0; i < wid; i++) {
            if (distTo[hei-1][i] < minEnergy) {
                minEnergy = distTo[hei-1][i];
                id = i;
            }
        }

        for (int i = hei-1; i >= 0; i--) {
            seam[i] = id;
            id = vertexTo[i][id];
        }

        return seam;
    }
 
    /**
     * Remove horizontal seam from current picture.
     * @param seam given seam to remove
     * @throws IllegalArgumentException unless seam is not a null, its length 
     * and its elements are in the prescribed range, and two adjacent entries
     * do not differ by more than 1.
     */
    public void removeHorizontalSeam(final int[] seam) {
        if (!isPictureTransposed) {
            transpose();
            isPictureTransposed = true;
        }
        isVerticalCalledFromHorizontal = true;
        removeVerticalSeam(seam);
        isVerticalCalledFromHorizontal = false;
    }
 
    /**
     * Remove vertical seam from current picture.
     * @param seam given seam to remove
     * @throws IllegalArgumentException unless seam is not a null, its length 
     * and its elements are in the prescribed range, and two adjacent entries
     * do not differ by more than 1.
     */
    public void removeVerticalSeam(final int[] seam) {
        validateForNull(seam);
        if (isPictureTransposed && !isVerticalCalledFromHorizontal) {
            transpose();
            isPictureTransposed = false;
        }
        validatePicture();
        validateSeam(seam);
        int hei = picture.height();
        int wid = picture.width();
        Picture newp = new Picture(wid-1, hei);
        for (int i = 0; i < hei; i++) {
            int j = 0;
            while (true) {
                if (j == seam[i]) break;
                newp.set(j, i, picture.get(j, i));
                j++;
            }
            int k = j;
            j++;
            while (j < wid) {
                newp.set(k, i, picture.get(j, i));
                j++;
                k++;
            }
        }
        
        picture = newp;
        wid--;
        double[][] newAEnergy = new double[hei][];
        for (int i = 0; i < hei; i++) {
            newAEnergy[i] = new double[wid];
        }
        aEnergy = newAEnergy;
        calculateEnergy();
    }

    /**
     * Test client for SeamCarver.
     * @param args the command-line arguments
     */
    public static void main(final String[] args) {
        SeamCarver sc = new SeamCarver(new Picture(args[0]));
        int[] seam = sc.findHorizontalSeam();
        System.out.println(Arrays.toString(seam));
        sc.removeHorizontalSeam(seam);
        seam = sc.findVerticalSeam();
        System.out.println(Arrays.toString(seam));
        sc.removeVerticalSeam(seam);
        sc.picture().show();
    }
 }