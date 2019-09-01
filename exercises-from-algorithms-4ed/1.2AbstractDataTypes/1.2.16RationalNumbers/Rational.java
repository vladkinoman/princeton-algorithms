import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

/*
*  Invariants
*  -----------
*   - gcd(num, den) = 1, i.e, the rational number is in reduced form
*   - den >= 1, the denominator is always a positive integer
*/

public class Rational
{
	private final long numerator;
	private final long denominator;

	Rational(long numerator, long denominator)
	{
		if(denominator == 0)
			throw new ArithmeticException("Division by zero!");
		/*assert numerator >= Long.MIN_VALUE &&numerator <= Long.MAX_VALUE 
			: "Overflow for the numerator";
		assert denominator >= Long.MIN_VALUE && denominator <= Long.MAX_VALUE 
			: "Overflow for the denominator";*/
		long g = gcd(numerator, denominator);
        numerator = numerator   / g;
        denominator = denominator / g;

		if(denominator < 0 && numerator >= 0)
		{
			denominator = -denominator;
			numerator = -numerator;
		}
		
		this.numerator = numerator;
		this.denominator = denominator;
	}

	public Rational plus(Rational b)
	{
		if(b == null)
			throw new NullPointerException("Second operand is a null.");
		Rational result;
		if(this.denominator == b.denominator)
			result = new Rational(numerator + b.numerator, denominator);
		else
			result = new Rational(numerator * b.denominator
				+ b.numerator * denominator, denominator * b.denominator);
		return result;
	}

	public Rational minus(Rational b)
	{
		if(b == null)
			throw new NullPointerException("Second operand is a null.");
		Rational result;
		if(this.denominator == b.denominator)
			result = new Rational(numerator - b.numerator, denominator);
		else
			result = new Rational(numerator * b.denominator
				- b.numerator * denominator, denominator * b.denominator);
		return result;
	}

	public Rational times(Rational b)
	{
		if(b == null)
			throw new NullPointerException("Second operand is a null.");
		return new Rational(numerator * b.numerator, 
			denominator * b.denominator);
	}

	public Rational divides(Rational b)
	{
		if(b == null)
			throw new NullPointerException("Second operand is a null.");
		if(b.numerator == 0)
			throw new ArithmeticException("Division by zero!");
		
		return new Rational(numerator * b.denominator, 
			denominator * b.numerator);
	}

	private static long gcd(long p, long q)
	{
		if(q == 0) return p;
		long r = p % q;
		return gcd(q, r);
	}

	public boolean equals(Object that)
	{
		if(this == that) return true;
		if(that == null) return false;
		if(this.getClass() != that.getClass()) return false;
		Rational other = (Rational) that;
		return (this.numerator == other.numerator 
			&& this.denominator == other.denominator); 
	} 

	public String toString()
	{
		if(numerator == 0 || denominator == 1)
			return numerator + "";
		return numerator + "/" + denominator;
	}

	public static void main(String[] args) {
		String[] sRational1 = StdIn.readLine().split("/");
		String[] sRational2 = StdIn.readLine().split("/");
		Rational a = new Rational(Long.parseLong(sRational1[0]), 
			Long.parseLong(sRational1[1]));
		Rational b = new Rational(Long.parseLong(sRational2[0]), 
			Long.parseLong(sRational2[1]));
		StdOut.printf("%s plus %s equals %s.\n", a, b, a.plus(b));
		StdOut.printf("%s minus %s equals %s.\n", a, b, a.minus(b));
		StdOut.printf("%s times %s equals %s.\n", a, b, a.times(b));
		Rational divResult;
		try
		{
			divResult = a.divides(b);
			StdOut.printf("%s divided by %s equals %s.\n", a, b, divResult);
		}
		catch(ArithmeticException e)
		{
			StdOut.printf("You can't divide by 0.\n");
		}
		if(a.equals(b))
			StdOut.printf("%s and %s are equal.\n", a, b);
		else
			StdOut.printf("%s and %s are not equal.\n", a, b);	  				
	}
}