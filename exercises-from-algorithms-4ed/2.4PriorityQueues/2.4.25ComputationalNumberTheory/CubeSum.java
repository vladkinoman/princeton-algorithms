import java.util.PriorityQueue;

public class CubeSum {

    private static class CubeSumTriplet implements Comparable {
        private int cubeSum;
        private int first;
        private int second;

        public CubeSumTriplet(int cubeSum, int first, int second) {
            this.cubeSum = cubeSum;
            this.first = first;
            this.second = second;
        }

        @Override
        public int compareTo(Object o) {
            CubeSumTriplet that = (CubeSumTriplet) o;
            if      (this.cubeSum < that.cubeSum) return -1;
            else if (this.cubeSum > that.cubeSum) return +1;
            return 0;
        }

        @Override
        public String toString() {
            return "{ "  + cubeSum +
                    ", " + first +
                    ", " + second +
                    " }";
        }
    }

    public static void printTriplets(int to) {
        PriorityQueue<CubeSumTriplet> pq = new PriorityQueue<>();
        int n = to;

        for (int i = 0; i <= n; i++) {
            pq.add(new CubeSumTriplet(i*i*i, i, 0));
        }

        int i = 0, j = 0;
        while (!pq.isEmpty()) {
            if (i > n) {
                i = 0;
                j++;
            }
            System.out.println(pq.remove());
            if (j < n) {
                pq.add(new CubeSumTriplet(i*i*i + (j+1)*(j+1)*(j+1), i, j+1));
            }
            i++;
        }
    }

    public static void main(String[] args) {
        printTriplets(10);
    }
}
