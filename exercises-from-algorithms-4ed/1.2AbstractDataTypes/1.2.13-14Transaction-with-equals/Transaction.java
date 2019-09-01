import edu.princeton.cs.algs4.Date;
import edu.princeton.cs.algs4.StdIn;
import edu.princeton.cs.algs4.StdOut;

public class Transaction
{
	private final String who;
	private final Date when;
	private final double amount;

	 /**
     * Initializes a new transaction from the given arguments.
     *
     * @param  who the person involved in this transaction
     * @param  when the date of this transaction
     * @param  amount the amount of this transaction
     * @throws IllegalArgumentException if {@code amount} 
     *         is {@code Double.NaN}, {@code Double.POSITIVE_INFINITY},
     *         or {@code Double.NEGATIVE_INFINITY}
     */
	Transaction(String who, Date when, double amount)
	{
		if (Double.isNaN(amount) || Double.isInfinite(amount))
            throw new IllegalArgumentException("Amount cannot be NaN or infinite");
		this.who = who;
		this.when = when;
		this.amount = amount;
	}

	/**
     * Initializes a new transaction by parsing a string of the form NAME DATE AMOUNT.
     *
     * @param  transaction the string to parse
     * @throws IllegalArgumentException if {@code amount} 
     *         is {@code Double.NaN}, {@code Double.POSITIVE_INFINITY},
     *         or {@code Double.NEGATIVE_INFINITY}
     */
	Transaction(String transaction)
	{
		String[] parsedTransaction = transaction.split("\\s+");

		this.who = parsedTransaction[0];
		this.when = new Date(parsedTransaction[1]);
		this.amount = Double.parseDouble(parsedTransaction[2]);
	}	

	public String who(){return who;}

	public Date when(){return when;}

	public double amount(){return amount;}

	/**
     * Returns a string representation of this transaction.
     *
     * @return a string representation of this transaction
     */
    @Override
	public String toString()
	{
		return String.format("%-10s %10s %8.2f", who, when, amount); 
	}

	/**
     * Compares this transaction to the specified object.
     *
     * @param  other the other transaction
     * @return true if this transaction is equal to {@code other}; false otherwise
     */
    @Override
	public boolean equals(Object that)
	{
		if(this == that) return true;
		if(that == null) return false; // not null
		if(this.getClass() != that.getClass()) return false; //1.reflexivity
		Transaction other = (Transaction) that; // that is y and other is z
		//3.transitivity (I suppose 2.symmetricity supported automatically)
		//we test hypothesis x.equals(z) == true, if so then implication is true 
		return (this.amount == other.amount) && (this.who.equals(other.who))
                                            && (this.when.equals(other.when));
	}

	public static void main(String[] args) {
		
		if(args[0].equals("full"))
		{
			Transaction transaction;
			String who = StdIn.readString();
			Date when = new Date(StdIn.readString());
			double amount = StdIn.readDouble();
			transaction = new Transaction(who, when, amount);
			if(transaction != null) StdOut.printf("%s\n", transaction);
		}
		else if(args[0].equals("string"))
		{
			Transaction transaction = new Transaction(StdIn.readLine());
			if(transaction != null) StdOut.printf("%s\n", transaction);
		}
		else if(args[0].equals("isequal"))
		{
			Transaction transaction1 = new Transaction(StdIn.readLine());
			Transaction transaction2 = new Transaction(StdIn.readLine());
			if(transaction1.equals(transaction2))
				StdOut.printf("Transactions are equal.");
			else
				StdOut.printf("Transactions are not equal.");
		}
		
	}
}