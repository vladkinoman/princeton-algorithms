/*@ requires x >= -2147483647;
	ensures \result >= 0;
	ensures x < 0 ==> \result == -x;
	ensures x >= 0 ==> \result == x;
*/
int abs(int x)
{
	if (x < 0)
		return -x;
	else
		return x;
}

int main(int a) {
	abs(a);
	return 0;
}
