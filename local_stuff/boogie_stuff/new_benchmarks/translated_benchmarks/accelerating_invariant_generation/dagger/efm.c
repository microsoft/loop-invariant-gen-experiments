//This example is adapted from StInG 
int main()
{
	int X1;
	int X2;
	int X3;
	int X4;
	int X5;
	int X6;

	if (! (X1>=1)) return;
	if (! (X2==0)) return;
	if (! (X3==0)) return;
	if (! (X4==1)) return;
	if (! (X5==0)) return;
	if (! (X6==0)) return;

	while(unknown())
	{
		if (unknown())
		{
			if (! (X1 >= 1)) return;
			if (! (X4 >= 1)) return;
			X1=X1-1;
			X4=X4-1;
			X2=X2+1;
			X5=X5+1;
		}
		else
		{
			if (unknown())
			{
				if (! (X2 >= 1)) return;
				if (! (X6 >= 1)) return;
				X2=X2-1;
				X3=X3+1;
			}
			else
			{
				if (unknown())
				{
					if (! (X4 >= 1)) return;
					if (! (X3 >= 1)) return;
					X3=X3-1;
					X2=X2+1;
				}
				else
				{
					if (unknown())
					{
						if (! (X3>=1)) return;
						X3=X3-1;
						X1=X1+1;
						X6=X6+X5;
						X5=0;
					}
					else
					{
						if (! (X2 >= 1)) return;
						X2 = X2 - 1;
						X1 = X1 + 1;
						X4 = X4 + X6;
						X6 = 0;
					}
				}
			}
		}
	}

	assert(X4 + X5 + X6 -1 >= 0); 
	assert(X4 + X5 + X6 -1 <= 0); 
	assert(X4 + X5 <= 1);
	assert(X5  >= 0);
	assert(X4  >= 0);
	assert(X3  >= 0);
	assert(X2  >= 0);
	assert(X1 + X5 >= 1);
	assert(X1 + X2 >= X4 + X5);
	assert(X1 + X2 + X3 >= 1);

}

