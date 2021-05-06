public class TestArray {

    public static boolean isMeanHeap(Comparable[] a) {
        int n = a.length - 1;
        for (int i = 1; i < n; i++) {
            if (a[i] == null) return false;
        }
        int i = 1;
        while (2*i <= n) {
            int j = 2*i;
            if (greater(a[i], a[j]) || j < n && greater(a[i], a[j+1])) {
                return false;
            }
            i = j;
        }
        return true;
    }

    private static boolean greater(Comparable a, Comparable b) {
        return a.compareTo(b) > 0;
    }

    public static void main(String[] args) {
        System.out.println(isMeanHeap((Comparable[]) new String[]{
                "-", "be", "not", "be", "to", "to", "or"}));
        System.out.println(isMeanHeap((Comparable[]) new String[]{
                "-", "be", "not", "be"}));
        System.out.println(isMeanHeap((Comparable[]) new String[]{
                "-", "be", "not"}));
        System.out.println(isMeanHeap((Comparable[]) new String[]{
                "-", "to", "be", "or", "not", "to", "be"}));
    }
}