public class SelectionSort {
    SelectionSort() {

    }

    /**
     * sort in ascending order
     *
     * we have to implement the invariants:
     * 1) i++
     * 2) finding the item which is greater than our min
     * 3) swap items
     *
     * @param a - input array
     */
    public static void sort(Comparable[] a) {
        int N = a.length;
        for (int i = 0; i < N; i++) {
            int min = i;
            for (int j = i + 1; j < N; j++) {
                if (less(a[j], a[min])) {
                    min = j;
                }
            }
            exch(a, i, min);
        }
    }

    private static void exch(Comparable[] a, int i, int j) {
        Comparable swap = a[i];
        a[i] = a[j];
        a[j] = swap;
    }

    /**
     *
     * @param v - first item
     * @param w - second item
     * @return true if the first item is less than second (v < w)
     */
    private static boolean less(Comparable v, Comparable w) {
        return v.compareTo(w) < 0;
    }

    public static void main(String[] args) {
        sort(new Comparable[] {10, 2, 4, 5, 1});

    }
}
