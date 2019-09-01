import java.util.*;

public class LnFactorial
{
	public static double lnFactorial(double N)
	{
		return Math.log(factorial(N));
	}
	private static double factorial(double N)
	{
		if(N == 0) return 1;
		else return N * factorial(N - 1);
	}
	public static void main(String[] args) {
		System.out.println(lnFactorial(Double.parseDouble(args[0])));
	}
}