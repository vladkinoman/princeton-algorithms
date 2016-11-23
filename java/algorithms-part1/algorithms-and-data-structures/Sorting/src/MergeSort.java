/**
 * Created by vbekl_000 on 11/23/2016.
 */
public class MergeSort {
    public static void merge(Comparable[] a, Comparable[] aux, int lo,
                      int mid, int hi) {
        assert isSorted(a, lo, mid);
        assert isSorted(a, mid+1, hi);

        // copy input to auxiliary
        for (int k = lo; k <= hi; k++) {
            aux[k] = a[k];
        }

        // merge two arrays
        int i = lo, j = mid+1;
        for (int k = lo; k <= hi; k++) {
            if (i > mid) a[k] = aux[j++];
            else if (j > hi) a[k] = aux[i++];
            else if (isless(aux[j], aux[i])) {
                a[k] = aux[j++];
            } else {
                a[k] = aux[i++];
            }
        }
        assert isSorted(a, lo, hi);
    }

    // v < r ---> - 1
    private static boolean isless(Comparable v, Comparable r) {
        return v.compareTo(r) < 0;
    }

    public void sort(Comparable[] a, int lo, int hi) {

    }

    public static boolean isSorted(Comparable[] a, int lo, int mid) {
        for (int i = lo; i <= mid - 1; i++) {
            if (isless(a[i+1], a[i])) {
                return false;
            }
        }
        return true;
    }

    public static void main(String[] args) {
        merge(new Comparable[] {1, 2, 3, 6, 8, 1, 4, 5, 7, 9},
                new Comparable[10],
                0, 4, 9);
    }
}
