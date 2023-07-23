import java.awt.Color;

import edu.princeton.cs.algs4.Picture;

public class SeamCarver {
    private Picture picture;
    private double[][] aEnergy;
    private double[][] distTo;
    private int[][] vertexTo;
    private boolean isPictureTransposed;
    private boolean isVerticalCalledFromHorizontal;

    // create a seam carver object based on the given picture
    public SeamCarver(final Picture picture) {
        validateForNull(picture);
        this.picture = new Picture(picture);
        int wid = picture.width();
        int hei = picture.height();
        calculateEnergy(picture, wid, hei);
        
        extracted(wid, hei);
        
    }

    private void calculateEnergy(final Picture picture, int wid, int hei) {
        aEnergy = new double[hei][];
        for (int i = 0; i < hei; i++) {
            aEnergy[i] = new double[wid];
            for (int j = 0; j < wid; j++) {
                if (i == 0 || i == hei-1 || j == 0 || j == wid-1) {
                    aEnergy[i][j] = 1000;
                } else {
                    Color cLeft = picture.get(j, i-1);
                    int iRxLeft = cLeft.getRed();
                    int iGxLeft = cLeft.getGreen();
                    int iBxLeft = cLeft.getBlue();
                    Color cRight = picture.get(j, i+1);
                    int iRxRight = cRight.getRed();
                    int iGxRight = cRight.getGreen();
                    int iBxRight = cRight.getBlue();

                    Color cUp = picture.get(j-1, i);
                    int iRyUp = cUp.getRed();
                    int iGyUp = cUp.getGreen();
                    int iByUp = cUp.getBlue();
                    Color cDown = picture.get(j+1, i);
                    int iRyDown = cDown.getRed();
                    int iGyDown = cDown.getGreen();
                    int iByDown = cDown.getBlue();

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
        int wid = height();
        int hei = width();
        double[][] newAEnergy = new double[hei][];
        double[][] newDistTo  = new double[hei][];
        int[][] newVertexTo   = new int[hei][];
        Picture newp = new Picture(wid, hei);
        for (int i = 0; i < hei; i++) {
            newAEnergy[i]  = new double[wid];
            newDistTo[i]   = new double[wid];
            newVertexTo[i] = new int[wid];
            for (int j = 0; j < wid; j++) {
                newAEnergy[i][j]  = aEnergy[j][i];
                newDistTo[i][j]   = distTo[j][i];
                newVertexTo[i][j] = vertexTo[j][i];
                newp.set(j, i, picture.get(i, j));
            }
        }
        aEnergy = newAEnergy;
        distTo = newDistTo;
        vertexTo = newVertexTo;
        picture = newp;
    }

    private void extracted(int wid, int hei) {
        distTo = new double[hei][];
        vertexTo = new int[hei][];
        for (int i = 0; i < hei; i++) {
            distTo[i] = new double[wid];
            vertexTo[i] = new int[wid];
            for (int j = 0; j < wid; j++) {
                distTo[i][j] = Double.POSITIVE_INFINITY;
                vertexTo[i][j] = -1;
            }
        }
        for (int m = 0; m < wid; m++) {
            distTo[0][m] = 0.0;
            
            for (int i = 0; i < hei; i++) {
                for (int j = 0; j < wid; j++) {
                    // doesn't work for wid=2
                    if (i == hei-1)
                    {
                        if (distTo[i][j] != Double.POSITIVE_INFINITY) {
                            distTo[i][j] += aEnergy[i][j];
                        }
                    } else if (j == 0) {
                        // only two edges
                        for (int k = 0; k < 2; k++) {
                            if (distTo[i+1][j+k] > distTo[i][j] + aEnergy[i][j])
                            {
                                distTo[i+1][j+k] = distTo[i][j] + aEnergy[i][j];
                                vertexTo[i+1][j+k] = j;
                            }
                        }
                    } else if (j == wid-1) {
                        // only two edges
                        for (int k = 0; k < 2; k++) {
                            if (distTo[i+1][j+k-1] > distTo[i][j] + aEnergy[i][j])
                            {
                                distTo[i+1][j+k-1] = distTo[i][j] + aEnergy[i][j];
                                vertexTo[i+1][j+k-1] = j;
                            }
                        }
                    } else if (i != hei-1) {
                        // three edges
                        for (int k = 0; k < 3; k++) {
                            if (distTo[i+1][j+k-1] > distTo[i][j] + aEnergy[i][j])
                            {
                                distTo[i+1][j+k-1] = distTo[i][j] + aEnergy[i][j];
                                vertexTo[i+1][j+k-1] = j;
                            }
                        }
                    }      
                }
            }

        }
    }

    private void validateForNull(Object obj) {
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

    private void validateSeam(final int[] seam, int hei, int wid) {
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

        for (int i = 0; i < seam.length-1; i++) {
            if (Math.abs(seam[i] - seam[i+1]) > 1) {
                throw new IllegalArgumentException(
                    "two adjacent seam entries differ by more than 1");
            }
        }
    }
 
    /**
     * Returns current picture.
     * 
     * @return current picture as Picture object
     */
    public final Picture picture() {
        return picture;
    }
 
    /**
     * Returns width of current picture.
     * 
     * @return width of current picture
     */
    public final int width() {
        return picture.width();
    }
 
    /**
     * Returns height of current picture.
     * 
     * @return height of current picture
     */
    public final int height() {
        return picture.height();
    }

    /**
     * Returns energy of pixel at column x and row y.
     * @param x x-coordinate of pixel
     * @param y y-coordinate of pixel
     * @return energy of pixel at column x and row y
     */
    public final double energy(final int x, final int y) {
        validateCoordinate(x, aEnergy[0].length);
        validateCoordinate(y, aEnergy.length);
        return aEnergy[y][x];
    }
 
    // sequence of indices for horizontal seam
    public final int[] findHorizontalSeam() {
        if (!isPictureTransposed) {
            transpose();
            isPictureTransposed = true;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        isVerticalCalledFromHorizontal = true;
        int[] result = findVerticalSeam();
        // still don't know how to make 2 transposes per 50 
        // consequtive horizontal seam removals
        if (isPictureTransposed) {
            transpose();
            isPictureTransposed = false;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        isVerticalCalledFromHorizontal = false;
        return result;
    }
 
    // sequence of indices for vertical seam
    public final int[] findVerticalSeam() {
        if (isPictureTransposed && !isVerticalCalledFromHorizontal) {
            transpose();
            isPictureTransposed = false;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        int hei = height();
        int wid = width();
        int[] seam = new int[hei];
        
        int id = -1;
        double minEnergy = Double.POSITIVE_INFINITY;
        for (int i = 0; i < wid; i++) {
            if (distTo[hei-1][i] < minEnergy) {
                minEnergy = distTo[hei-1][i];
                id = i;
            }
        }

        for (int i = hei-1; i >= 0 ; i--) {
            seam[i] = id;
            id = vertexTo[i][id];
        }

        return seam;
    }
 
    // remove horizontal seam from current picture
    public void removeHorizontalSeam(final int[] seam) {
        if (!isPictureTransposed) {
            transpose();
            isPictureTransposed = true;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        isVerticalCalledFromHorizontal = true;
        removeVerticalSeam(seam);
        // still don't know how to make 2 transposes per 50 
        // consequtive horizontal seam removals
        if (isPictureTransposed) {
            transpose();
            isPictureTransposed = false;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        isVerticalCalledFromHorizontal = false;
    }
 
    // remove vertical seam from current picture
    public void removeVerticalSeam(final int[] seam) {
        validateForNull(seam);
        validatePicture();
        if (isPictureTransposed && !isVerticalCalledFromHorizontal) {
            transpose();
            isPictureTransposed = false;
            calculateEnergy(picture, picture.width(), picture.height());
            extracted(picture.width(), picture.height());
        }
        int hei = height();
        int wid = width();
        validateSeam(seam, hei, wid);
        
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
                j++; k++;
            }
        }
        
        picture = newp;

        double[][] newAEnergy = new double[hei][];
        for (int i = 0; i < hei; i++) {
            newAEnergy[i] = new double[wid-1];
            //System.arraycopy(aEnergy[i], 0, newAEnergy[i], 0, seam[i]);
            //System.arraycopy(aEnergy[i], seam[i]+1, newAEnergy[i], seam[i], wid-seam[i]-1);
        }
        aEnergy = newAEnergy;
        calculateEnergy(picture, wid-1, hei);
        extracted(wid-1, hei);
        isVerticalCalledFromHorizontal = false;
    }

    //  unit testing (optional)
    public static void main(final String[] args) {
        SeamCarver sc = new SeamCarver(new Picture(args[0]));
        System.out.println(sc.energy(1, 2));
        System.out.println(java.util.Arrays.toString(sc.findVerticalSeam()));
        sc.removeVerticalSeam(sc.findVerticalSeam());
        sc.picture().show();
    }
 }