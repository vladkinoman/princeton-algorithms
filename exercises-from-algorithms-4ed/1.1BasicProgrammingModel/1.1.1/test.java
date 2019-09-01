import java.lang.*;

public class test{
	public static String exR2(int n)
	{
		String s = exR2(n-3) + n + exR2(n-2) + n;
		if (n <= 0) return "";
		return s;
	}

	public static void main(String[] args) {
		System.out.println(exR2(Integer.parseInt(args[0])));	
	}
}