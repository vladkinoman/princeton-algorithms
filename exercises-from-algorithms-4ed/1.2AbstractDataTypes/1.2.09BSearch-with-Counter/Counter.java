public class Counter
{
	private int count;
	private final String name;

	 /**
     * Initializes a new counter starting at 0, with the given id.
     *
     * @param id the name of the counter
     */
    public Counter(String id) {
        name = id;
    }

	public int tally()
	{
		return count;
	}

	public void increment()
	{
		count++;
	}

	public String toString() {
        return count + " " + name;
    } 

}