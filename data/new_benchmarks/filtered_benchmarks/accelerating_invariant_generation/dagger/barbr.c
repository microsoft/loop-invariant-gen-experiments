// This example is adapted from StInG
int main()
{
	int barber;
	int chair;
	int open;
	int p1;
	int p2;
	int p3;
	int p4;
	int p5;

	barber = 0;
	chair = 0;
	open = 0;
	p1 = 0;
	p2 = 0;
	p3 = 0;
	p4 = 0;
	p5 = 0;

	while (unknown())
	{
		if (unknown())
		{
			if (!(p1 >= 0))
				return;
			if (!(p1 <= 0))
				return;
			if (!(barber >= 1))
				return;
			barber = barber - 1;
			chair = chair + 1;
			p1 = 1;
		}
		else
		{
			if (unknown())
			{
				if (!(p2 >= 0))
					return;
				if (!(p2 <= 0))
					return;
				if (!(barber >= 1))
					return;
				barber = barber - 1;
				chair = chair + 1;
				p2 = 1;
			}
			else
			{
				if (unknown())
				{
					if (!(p2 >= 1))
						return;
					if (!(p2 <= 1))
						return;
					if (!(open >= 1))
						return;
					open = open - 1;
					p2 = 0;
				}
				else
				{
					if (unknown())
					{
						if (!(p3 >= 0))
							return;
						if (!(p3 <= 0))
							return;
						if (!(barber >= 1))
							return;
						barber = barber - 1;
						chair = chair + 1;
						p3 = 1;
					}
					else
					{
						if (unknown())
						{
							if (!(p3 >= 1))
								return;
							if (!(p3 <= 1))
								return;
							if (!(open >= 1))
								return;
							open = open - 1;
							p3 = 0;
						}
						else
						{
							if (unknown())
							{
								if (!(p4 >= 0))
									return;
								if (!(p4 <= 0))
									return;
								if (!(barber >= 1))
									return;
								barber = barber - 1;
								chair = chair + 1;
								p4 = p4 + 1;
							}
							else
							{
								if (unknown())
								{
									if (!(p4 >= 1))
										return;
									if (!(p4 <= 1))
										return;
									if (!(open >= 1))
										return;
									open = open - 1;
									p4 = p4 - 1;
								}
								else
								{
									if (unknown())
									{
										if (!(p5 >= 0))
											return;
										if (!(p5 <= 0))
											return;
										barber = barber + 1;
										p5 = 1;
									}
									else
									{
										if (unknown())
										{
											if (!(p5 >= 1))
												return;
											if (!(p5 <= 1))
												return;
											if (!(chair >= 1))
												return;
											chair = chair - 1;
											p5 = 2;
										}
										else
										{
											if (unknown())
											{
												if (!(p5 >= 2))
													return;
												if (!(p5 <= 2))
													return;
												open = open + 1;
												p5 = 3;
											}
											else
											{
												if (unknown())
												{
													if (!(p5 >= 3))
														return;
													if (!(p5 <= 3))
														return;
													if (!(open == 0))
														return;
													p5 = 0;
												}
												else
												{
													if (!(p1 >= 1))
														return;
													if (!(p1 <= 1))
														return;
													if (!(open >= 1))
														return;
													open = open - 1;
													p1 = 0;
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
	assert(p5 >= open);
	assert(p1 <= 1);
	assert(p2 <= 1);
	assert(p3 <= 1);
	assert(p4 <= 1);
	assert(p5 <= 3);
	assert(p4 >= 0);
	assert(p3 >= 0);
	assert(p2 >= 0);
	assert(p1 >= 0);
	assert(open >= 0);
	assert(chair >= 0);
	assert(barber >= 0);
}
