import java.lang.System;

public class Euclid
{
	public static int gcd(int p, int q)
	{
		System.out.println(p + " " + q);
		if (q == 0) return p; // base case
		int r = p % q;
		return gcd(q, r);
	}

	public static int gcdNoDivision(int p, int q)
	{
		while(p != q)
		{
			System.out.println(p + " " + q);
			if(p < q)
			{
				int tmp = p;
				p = q;
				q = tmp;
			}
			p = p - q;
		}
		return p;
	}

	public static void main(String[] args) {
		if(args[0].equals("/"))
			System.out.println(gcd(Integer.parseInt(args[1]),
		 		Integer.parseInt(args[2])));
		else if (args[0].equals("-"))
			System.out.println(gcdNoDivision(Integer.parseInt(args[1]),
		 		Integer.parseInt(args[2])));
	}
}