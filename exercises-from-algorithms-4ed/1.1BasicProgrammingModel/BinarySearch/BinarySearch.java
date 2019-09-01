import java.lang.*;
import java.util.Arrays;

public class BinarySearch
{
	public static int rank(int key, int[] a)
	{
		int lo = 0;
		int hi = a.length - 1;
		int mid = 0;
		while(lo <= hi)
		{
			mid = lo + (hi - lo) / 2 ;
			if (a[mid] > key) hi = mid - 1;
			else if (a[mid] < key) lo = mid + 1;
			else return mid;
		}
		return -1;
	}

	public static void main(String[] args) {
		int key = Integer.parseInt(args[0]);
		int[] inputArr = new int[args.length-1];

		for (int i = 0; i < inputArr.length ; i++)
			inputArr[i] = Integer.parseInt(args[i+1]);

		Arrays.sort(inputArr);

		System.out.println(rank(key, inputArr));
	}
}