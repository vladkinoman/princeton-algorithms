import java.lang.System;

public class CircularRotation
{
	/*my own solution*/
	private static boolean isCircularlyShifted(String s1, String s2)
	{
		if(s1.length() != s2.length())
		{
			for(int i = 0; i < s1.length(); i++)
				s2 = s2 + s2.charAt(i);
		
			if(s2.indexOf(s1) != -1)
				return true;
		}
		return false;
	}

	/*solution from the authors*/
	private static boolean isCircularlyShiftedAlgs4(String s, String t)
	{
		return (s.length() == t.length()) && (s.concat(s).indexOf(t) >= 0);
	}

	public static void main(String[] args) {
		String s1 = args[0];
		String s2 = args[1];
		
		if(isCircularlyShifted(s1, s2)) 
			System.out.println("Yes!");
		else System.out.println("No!");

		if(isCircularlyShiftedAlgs4(s1, s2)) 
			System.out.println("Yes (algs4)!");
		else System.out.println("No (algs4)!");
	}
}