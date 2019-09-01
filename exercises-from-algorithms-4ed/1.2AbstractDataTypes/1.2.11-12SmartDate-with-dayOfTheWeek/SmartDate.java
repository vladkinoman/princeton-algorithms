import java.lang.String;


public class SmartDate
{
	private final int month;
	private final int day;
	private final int year; 

	private void checkSmartDate()
	{
		if(month < 1 || month > 12
			|| day < 1 || day > 31 
			|| year < 0)
			throw new IllegalArgumentException("Date is not legal.");
	}

	SmartDate(int month, int day, int year)
	{
		this.month = month;
		this.day = day;
		this.year = year;
		checkSmartDate();
	}

	SmartDate(String date)
	{
		String[] input = date.split("/");
		if(input.length != 3)
			throw new IllegalArgumentException("Date is not legal.");

		month = Integer.parseInt(input[0]);
		day   = Integer.parseInt(input[1]);
		year  = Integer.parseInt(input[2]);

		checkSmartDate();
	}

	public int month()
	{
		return month;
	}

	public int day()
	{
		return day;
	}

	public int year()
	{
		return year;
	}

	public String dayOfTheWeek()
	{
		
	}

	public String toString()
	{
		return month + "/" + day + "/" + year;
	}

	public static void main(String[] args) {
		SmartDate sdate = new SmartDate(args[0]);
		System.out.println(sdate);
	}
}