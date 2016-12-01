int count(int * a, int N)
{
	int x = 0; 
	int i = 0;

	while (i < N)
	{
		if (i % 2 != 0 && a[i] % 2 != 0)
		{
			x = x + 1;
			i = i + 1;
		}
		else
		{
			i = i + 1;
		}
	}

	return x;
}
	
