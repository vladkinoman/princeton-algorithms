import edu.princeton.cs.algs4.StdRandom;

public class Shuffling {
    public static void sort(Comparable[] a) {
        for (int i = 0; i < a.length; i++) {
            //
            // between 0 and i inclusive
            int r = StdRandom.uniform(i + 1);
            exch(a, i, r);
        }
    }

    private static void exch(Comparable[] a, int i, int j) {
        Comparable swap = a[i];
        a[i] = a[j];
        a[j] = swap;
    }
}
