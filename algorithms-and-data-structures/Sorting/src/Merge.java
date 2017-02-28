/**
 * This is stable algorithm.
 * Running time proportional to n lg n (best, average and worst case)
 *  O(n) for ordered array
 */
public class Merge {
    public static void merge(Comparable[] a, Comparable[] aux, int lo,
                      int mid, int hi) {
        // helps detect logic bugs and documents code
        assert isSorted(a, lo, mid);
        assert isSorted(a, mid+1, hi);

        // copy input to auxiliary
        for (int k = lo; k <= hi; k++) {
            aux[k] = a[k];
        }

        // merge two arrays
        int i = lo, j = mid+1;
        for (int k = lo; k <= hi; k++) {
            if (i > mid)                        a[k] = aux[j++];
            else if (j > hi)                    a[k] = aux[i++];
            else if (isless(aux[j], aux[i]))    a[k] = aux[j++];
            else                                a[k] = aux[i++];
        }

        assert isSorted(a, lo, hi);
    }

    // v < w ---> - 1
    private static boolean isless(Comparable v, Comparable w) {
        return v.compareTo(w) < 0;
    }

    public static void sort(Comparable[] a, Comparable[] aux, int lo, int hi) {
        if (hi <= lo) return;
        // left part is greater than right
        int mid = lo + (hi - lo) / 2;
        sort(a, aux, lo, mid);
        sort(a, aux, mid+1, hi);
        merge(a, aux, lo, mid, hi);
    }

    public static boolean isSorted(Comparable[] a, int lo, int hi) {
        for (int i = lo; i <= hi - 1; i++) {
            if (isless(a[i+1], a[i])) {
                return false;
            }
        }
        return true;
    }

    public static void main(String[] args) {
        Comparable[] a = new Comparable[] {1, 2, 3, 6, 8, 1, 4, 5, 7, 9};
        Shuffling.sort(a);
        Merge.sort(a, new Comparable[10], 0, 9);
        assert isSorted(a, 0, 9);
    }
}
