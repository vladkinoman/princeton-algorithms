import edu.princeton.cs.algs4.StdIn;

import java.util.Iterator;

public class Subset {
    public static void main(String[] args) {
        int k = Integer.parseInt(args[1]);
        RandomizedQueue<String> srq = new RandomizedQueue<>();
        StdIn.readString();
        while (!StdIn.isEmpty())
        {
            String s = StdIn.readString();
            srq.enqueue(s);
        }
        if (k > srq.size() || k < 0) {
            throw new java.util.NoSuchElementException("k must be greater" +
                    " than 0 and less and equal N (count of strings)");
        }
        Iterator<String> iter = srq.iterator();
        for (int i = 0; i < k; i++) {
            System.out.println(iter.next());
        }
    }
}
