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
    public SeamCarver(Picture picture) {
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
                    calculateEnergyOfInnerPixel(
                        aRGB[i-1][j], aRGB[i+1][j], aRGB[i][j-1], aRGB[i][j+1],
                        i, j
                    );
                }
            }
        }
    }

    private void calculateEnergyOfInnerPixel(int left, int right, int up, int down,
        int i, int j) {
        int iRxLeft  = (left >> 16) & 0xFF;
        int iGxLeft  = (left >> 8) & 0xFF;
        int iBxLeft  = (left >> 0) & 0xFF;
        int iRxRight = (right >> 16) & 0xFF;
        int iGxRight = (right >> 8) & 0xFF;
        int iBxRight = (right >> 0) & 0xFF;
        int iRyUp    = (up >> 16) & 0xFF;
        int iGyUp    = (up >> 8) & 0xFF;
        int iByUp    = (up >> 0) & 0xFF;
        int iRyDown  = (down >> 16) & 0xFF;
        int iGyDown  = (down >> 8) & 0xFF;
        int iByDown  = (down >> 0) & 0xFF;
        aEnergy[i][j] = Math.sqrt(
            (iRxRight-iRxLeft)*(iRxRight-iRxLeft)
          + (iGxRight-iGxLeft)*(iGxRight-iGxLeft) 
          + (iBxRight-iBxLeft)*(iBxRight-iBxLeft)
          + (iRyDown-iRyUp)*(iRyDown-iRyUp)
          + (iGyDown-iGyUp)*(iGyDown-iGyUp)
          + (iByDown-iByUp)*(iByDown-iByUp)
        );
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

        int[] seam = new int[hei];

        if (hei <= 2 || wid <= 2) {
            // this is the case when each energy equals 1000,
            // b/c we don't have inner part, just border
            // it's all we need if we want to remove first col/row
            // array is initialized explicitly in order to remove the warning
            Arrays.fill(seam, 0);
            return seam;
        }

        double[][] distTo = new double[hei][];
        int[][] vertexTo = new int[hei][];
        for (int i = 0; i < hei; i++) {
            distTo[i] = new double[wid];
            vertexTo[i] = new int[wid];
            for (int j = 0; j < wid; j++) {
                distTo[i][j] = Double.POSITIVE_INFINITY;
                vertexTo[i][j] = -1; // placeholder value since we don't use it
            }
        }
        allPairsSP(distTo, vertexTo);

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
        
        for (int i = 0; i < hei; i++) {
            System.arraycopy(aEnergy[i], seam[i]+1, aEnergy[i], seam[i],
             wid-seam[i]-1);
        }
        --wid;
        for (int i = 0; i < hei; i++) {
            int j = seam[i];
            if (j == wid) --j;
            if (i == 0 || i == hei-1 || j == 0 || j == wid-1) {
                aEnergy[i][j] = 1000;
                if (j-1 > 0 && i != 0 && i != hei-1) {
                    calculateEnergyOfInnerPixel(
                        picture.get(j-2, i).getRGB(),
                        picture.get(j, i).getRGB(),
                        picture.get(j-1, i-1).getRGB(),
                        picture.get(j-1, i+1).getRGB(),
                        i, j-1
                    );
                }
            } else {
                calculateEnergyOfInnerPixel(
                    picture.get(j-1, i).getRGB(),
                    picture.get(j+1, i).getRGB(),
                    picture.get(j, i-1).getRGB(),
                    picture.get(j, i+1).getRGB(),
                    i, j
                );
                
                if (j-1 > 0) {
                    calculateEnergyOfInnerPixel(
                        picture.get(j-2, i).getRGB(),
                        picture.get(j, i).getRGB(),
                        picture.get(j-1, i-1).getRGB(),
                        picture.get(j-1, i+1).getRGB(),
                        i, j-1
                    );
                }
                if (i-1 > 0) {
                    calculateEnergyOfInnerPixel(
                        picture.get(j-1, i-1).getRGB(),
                        picture.get(j+1, i-1).getRGB(),
                        picture.get(j, i-2).getRGB(),
                        picture.get(j, i).getRGB(),
                        i-1, j
                    );
                }
                if (i+1 < hei-1) {
                    calculateEnergyOfInnerPixel(
                        picture.get(j-1, i+1).getRGB(),
                        picture.get(j+1, i+1).getRGB(),
                        picture.get(j, i).getRGB(),
                        picture.get(j, i+2).getRGB(),
                        i+1, j
                    );
                }
            }
        }
    }

    /**
     * Test client for SeamCarver.
     * @param args the command-line arguments
     */
    public static void main(final String[] args) {        
        SeamCarver carver = new SeamCarver(new Picture(args[0]));
        // carver.removeVerticalSeam(new int[]{ 4, 5, 6, 5, 6, 6, 5, 5, 6, 6 }); // 7x10
        int[] seam = carver.findHorizontalSeam();
        System.out.println(Arrays.toString(seam));
        carver.removeHorizontalSeam(seam);
        seam = carver.findVerticalSeam();
        System.out.println(Arrays.toString(seam));
        carver.removeVerticalSeam(seam);
        carver.picture().show();
        // just a random picture from one of the tests
        // Picture picture = new Picture(6, 6);
        
        // picture.set(0, 0, new java.awt.Color(0x050803));
        // picture.set(1, 0, new java.awt.Color(0x090008));
        // picture.set(2, 0, new java.awt.Color(0x080302));
        // picture.set(3, 0, new java.awt.Color(0x090505));
        // picture.set(4, 0, new java.awt.Color(0x040100));
        // picture.set(5, 0, new java.awt.Color(0x010407));
        
        // picture.set(0, 1, new java.awt.Color(0x060204));
        // picture.set(1, 1, new java.awt.Color(0x090608));
        // picture.set(2, 1, new java.awt.Color(0x050807));
        // picture.set(3, 1, new java.awt.Color(0x000407));
        // picture.set(4, 1, new java.awt.Color(0x040405));
        // picture.set(5, 1, new java.awt.Color(0x050900));

        // picture.set(0, 2, new java.awt.Color(0x070604));
        // picture.set(1, 2, new java.awt.Color(0x000109));
        // picture.set(2, 2, new java.awt.Color(0x060209));
        // picture.set(3, 2, new java.awt.Color(0x030301));
        // picture.set(4, 2, new java.awt.Color(0x010503));
        // picture.set(5, 2, new java.awt.Color(0x060303));
        
        // picture.set(0, 3, new java.awt.Color(0x070406));
        // picture.set(1, 3, new java.awt.Color(0x030300));
        // picture.set(2, 3, new java.awt.Color(0x060903));
        // picture.set(3, 3, new java.awt.Color(0x050304));
        // picture.set(4, 3, new java.awt.Color(0x090900));
        // picture.set(5, 3, new java.awt.Color(0x080405));
        
        // picture.set(0, 4, new java.awt.Color(0x000407));
        // picture.set(1, 4, new java.awt.Color(0x030504));
        // picture.set(2, 4, new java.awt.Color(0x040405));
        // picture.set(3, 4, new java.awt.Color(0x070202));
        // picture.set(4, 4, new java.awt.Color(0x010402));
        // picture.set(5, 4, new java.awt.Color(0x080903));
        
        // picture.set(0, 5, new java.awt.Color(0x070607));
        // picture.set(1, 5, new java.awt.Color(0x060209));
        // picture.set(2, 5, new java.awt.Color(0x090502));
        // picture.set(3, 5, new java.awt.Color(0x010409));
        // picture.set(4, 5, new java.awt.Color(0x080705));
        // picture.set(5, 5, new java.awt.Color(0x060604));
        // SeamCarver carver = new SeamCarver(picture);
        // carver.picture().show();
    }
 }