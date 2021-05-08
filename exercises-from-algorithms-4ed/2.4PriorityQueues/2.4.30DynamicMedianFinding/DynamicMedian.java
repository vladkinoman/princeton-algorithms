import java.util.Comparator;
import java.util.NoSuchElementException;
import java.util.PriorityQueue;

public class DynamicMedian {

    private PriorityQueue<Integer> pqMax;
    private PriorityQueue<Integer> pqMin;

    public DynamicMedian() {
        pqMax = new PriorityQueue<>(new Comparator<Integer>() {
            @Override
            public int compare(Integer k1, Integer k2) {
                if (k1 < k2) return +1;
                if (k1.equals(k2)) return 0;
                return -1;
            }
        });
        pqMin = new PriorityQueue<>();
    }

    public void insert(int key) {
        if (!pqMin.isEmpty() && pqMin.element() < key ||
                pqMin.isEmpty() && !pqMax.isEmpty()) {
            pqMin.add(key);
        } else {
            pqMax.add(key);
        }

        if (pqMax.size() < pqMin.size()) {
            pqMax.add(pqMin.remove());
        }
    }

    public double find() {
        if (pqMax.isEmpty()) throw new NoSuchElementException();

        if (pqMax.size() == pqMin.size()) {
            return (pqMax.element() + pqMin.element())/2.0;
        }

        return pqMax.element();
    }

    public double remove() {
        if (pqMax.isEmpty()) throw new NoSuchElementException();

        if (pqMax.size() == pqMin.size()) {
            return (pqMax.remove() + pqMin.remove())/2.0;
        }

        return pqMax.remove();
    }

    public static void main(String[] args) {
        DynamicMedian dm = new DynamicMedian();
        dm.insert(1);
        dm.insert(2);
        dm.insert(3);
        dm.insert(4);
        dm.insert(5);
        dm.insert(6);
        dm.insert(8);
        dm.insert(9);
        dm.remove(); // remove 4 and 5, leave 3 and 6
        System.out.println("median = " + dm.find());

        DynamicMedian dm2 = new DynamicMedian();
        dm2.insert(1);
        dm2.insert(3);
        dm2.insert(2);
        System.out.println("median = " + dm2.find());
    }
}
