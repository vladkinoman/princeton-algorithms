import edu.princeton.cs.algs4.AcyclicSP;
import edu.princeton.cs.algs4.Picture;

public class SeamCarver {
    private Picture picture;
    private AcyclicSP asp;
    private double[][] aEnergy;
    // create a seam carver object based on the given picture
    public SeamCarver(final Picture picture) {
        validateForNull(picture);
        this.picture = new Picture(picture);
        int w = picture.width();
        int h = picture.height();
        aEnergy = new double[h][];
        for (int i = 0; i < h; i++) {
            aEnergy[i] = new double[w];
            for (int j = 0; j < w; j++) {
                if (i == 0 || i == h-1 || j == 0 || j == w-1) {
                    aEnergy[i][j] = 1000;
                } else {
                    int iRxLeft = picture.get(j, i-1).getRed();
                    int iGxLeft = picture.get(j, i-1).getGreen();
                    int iBxLeft = picture.get(j, i-1).getBlue();
                    int iRxRight = picture.get(j, i+1).getRed();
                    int iGxRight = picture.get(j, i+1).getGreen();
                    int iBxRight = picture.get(j, i+1).getBlue();

                    int iRyUp = picture.get(j-1, i).getRed();
                    int iGyUp = picture.get(j-1, i).getGreen();
                    int iByUp = picture.get(j-1, i).getBlue();
                    int iRyDown = picture.get(j+1, i).getRed();
                    int iGyDown = picture.get(j+1, i).getGreen();
                    int iByDown = picture.get(j+1, i).getBlue();

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

    private void validateForNull(Object obj) {
        if (obj == null) {
            throw new IllegalArgumentException(
                "the argument is null");
        }
    }

    private void validateCoordinate(final int x) {
        if (x < 0 || x > picture.width() - 1) {
            throw new IllegalArgumentException(
                "the coordinate is outside its prescribed range.");
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

    // energy of pixel at column x and row y
    public final double energy(final int x, final int y) {
        validateCoordinate(x);
        validateCoordinate(y);
        return aEnergy[y][x];
    }
 
    // sequence of indices for horizontal seam
    public final int[] findHorizontalSeam() {
        return null;

    }
 
    // sequence of indices for vertical seam
    public final int[] findVerticalSeam() {
        return null;

    }
 
    // remove horizontal seam from current picture
    public void removeHorizontalSeam(final int[] seam) {
        validateForNull(seam);
        if (seam.length != picture.width()) {
            throw new IllegalArgumentException("the array of the wrong length");
        }
        // not a valid seam, throw IllegalArg here
        // either an entry is outside its prescribed range or
        // two adjacent entries differ by more than 1

        if (picture.height() <= 1) {
            throw new IllegalArgumentException(
                "the height of the picture is less than or equal to 1");
        }
    }
 
    // remove vertical seam from current picture
    public void removeVerticalSeam(final int[] seam) {
        validateForNull(seam);
        if (seam.length != picture.height()) {
            throw new IllegalArgumentException("the array of the wrong length");
        }
        // not a valid seam, throw IllegalArg here
        // either an entry is outside its prescribed range or
        // two adjacent entries differ by more than 1

        if (picture.width() <= 1) {
            throw new IllegalArgumentException(
                "the width of the picture is less than or equal to 1");
        }
    }
 
    //  unit testing (optional)
    public static void main(final String[] args) {
        SeamCarver sc = new SeamCarver(new Picture(args[0]));
        System.out.println(sc.energy(1, 2));
    }
 }