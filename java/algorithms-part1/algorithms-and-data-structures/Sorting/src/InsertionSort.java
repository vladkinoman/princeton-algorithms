/**
 * Created by vbekl_000 on 11/22/2016.
 */
public class InsertionSort {

    public static void sort(Comparable[] a) {
        int N = a.length;
        for (int i = 0; i < a.length; i++) {
            for (int j = i; j > 0; j--) {
                if (less(a[j], a[j-1])) {
                    exch(a, j, j-1);
                    break;
                }
            }
        }
    }

    private static void exch(Comparable[] a, int j, int i) {
        Comparable swap = a[j];
        a[j] = a[i];
        a[i] = swap;
    }

    private static boolean less(Comparable c1, Comparable c2) {
        return c1.compareTo(c2) < 0;
    }

    public static void main(String[] args) {
        sort(new Comparable[]{5, 2, 1, 6});
    }
}
