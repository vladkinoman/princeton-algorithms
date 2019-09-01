import java.lang.*;

public class LgNoMath
{
	public static int lg(int N)
	{
		int i;
		for (i = 0; N > 1 ; i++, N /= 2)
			;
		return i;
	}

	public static void main(String[] args) {
		System.out.println(lg(Integer.parseInt(args[0])));
	}
}