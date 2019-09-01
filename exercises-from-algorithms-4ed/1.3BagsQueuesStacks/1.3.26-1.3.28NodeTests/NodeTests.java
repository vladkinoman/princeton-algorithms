public class NodeTests
{
	private static class NodeString
	{
		NodeString next;
		String item;
	}

	private static class NodeInt
	{
		NodeInt next;
		int item;
	}
	
	public static NodeString removeAll(NodeString first, String key)
	{
		NodeString prev = null;
		for(NodeString i = first; i != null; i = i.next)
		{
			if(i.item.equals(key))
			{
				if(prev != null) prev.next = i.next;
				else     		 first = first.next;
			}
			else prev = i;
		}
		return first;
	}

	public static void print(NodeString first)
	{
		for(NodeString i = first; i != null; i = i.next)
		{
			System.out.print(i.item + " ");
		}
		System.out.println();	
	}

	public static void iprint(NodeInt first)
	{
		for(NodeInt i = first; i != null; i = i.next)
		{
			System.out.print(i.item + " ");
		}
		System.out.println();	
	}

	public static int max(NodeInt first)
	{
		if(first == null) return 0;
		int max = max(first.next);
		if(first.item > max) return first.item;
		else return max;
	}

	public NodeTests()
	{
		
	}

	public static void main(String[] args) {
		NodeString first = new NodeString();
		first.item = "to";
		first.next = new NodeString();
		first.next.item = "be";
		first.next.next = new NodeString();
		first.next.next.item = "to";
		first.next.next.next = null;
		print(first);
		first = removeAll(first, "to");
		print(first);

		NodeInt ifirst = new NodeInt();
		ifirst.item = 1;
		ifirst.next = new NodeInt();
		ifirst.next.item = 4;
		ifirst.next.next = new NodeInt();
		ifirst.next.next.item = 1;
		ifirst.next.next.next = new NodeInt();
		ifirst.next.next.next.item = 2;
		ifirst.next.next.next.next = null;
		iprint(ifirst);
		System.out.println("max = " + max(ifirst));
	}
}