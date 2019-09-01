import java.lang.*;

public class PrintBooleanArray
{
	private static boolean[] arr;

	public static void main(String[] args) {
		arr = new boolean[args.length+1];
		
		for (int i = 0; i < args.length; i++)
			arr[i] = Boolean.parseBoolean(args[i]);

		for (int i = 0; i < arr.length ; i++)
			if(arr[i])
				System.out.print("*");
			else
				System.out.print(" ");
		System.out.println();
	}
}