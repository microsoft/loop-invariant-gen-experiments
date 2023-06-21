int main()
{

	int x;
	int y;
	int xa = 0;
	int ya = 0;

	while (unknown())
	{
		x = xa + 2 * ya;
		y = -2 * xa + ya;

		x++;
		if (unknown())
			y = y + x;
		else
			y = y - x;

		xa = x - 2 * y;
		ya = 2 * x + y;
	}

	assert(xa + 2 * ya >= 0);
}
