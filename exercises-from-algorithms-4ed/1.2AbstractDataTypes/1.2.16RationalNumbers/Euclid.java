import edu.princeton.cs.algs4.StdOut;

public class Euclid
{
	public static int gcd(int p, int q)
	{
		if(q == 0) return p;
		int r = p % q;
		return gcd(q, r);
	}

	public static void main(String[] args) {
		StdOut.printf("gcd(%s, %s) = %d",args[0], args[1],
			gcd(Integer.parseInt(args[0]), Integer.parseInt(args[1])));
	}
}