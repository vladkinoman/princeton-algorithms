import edu.princeton.cs.algs4.StdIn;

import java.util.Iterator;

public class Subset {
    public static void main(String[] args) {
        int k = Integer.parseInt(args[0]);
        RandomizedQueue<String> srq = new RandomizedQueue<>();
        while (!StdIn.isEmpty())
        {
            String s = StdIn.readString();
            srq.enqueue(s);
        }
        Iterator<String> iter = srq.iterator();
        for (int i = 0; i < k; i++) {
            System.out.println(iter.next());
        }
    }
}
