#include "myassert.h"

int nondet_int();

//This example is adapted from StInG 
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

	barber=0;
	chair=0;
	open=0;
	p1=0;
	p2=0;
	p3=0;
	p4=0;
	p5=0;

	while(nondet_int())
	{
		if (nondet_int())
		{
			if (!(p1 >= 0)) return;
			if (!(p1 <= 0)) return;
			if (!(barber >= 1)) return;
			barber = barber-1;
			chair = chair+1;
			p1 = 1;
		}
		else
		{
			if (nondet_int())
			{
				if (!(p2 >= 0)) return;
				if (!(p2 <= 0)) return;
				if (!(barber >= 1)) return;
				barber = barber-1;
				chair = chair+1;
				p2 = 1;
			}
			else
			{
				if (nondet_int())
				{
					if (!(p2 >= 1)) return;
					if (!(p2 <= 1)) return;
					if (!(open >=1)) return;
					open = open -1;
					p2 = 0;
				}
				else
				{
					if (nondet_int())
					{
						if (!(p3>=0)) return;
						if (!(p3<=0)) return;
						if (!(barber >=1)) return;
						barber = barber-1;
						chair = chair +1;
						p3 =1;
					}
					else
					{
						if (nondet_int())
						{
							if (!(p3>=1)) return;
							if (!(p3<=1)) return;
							if (!(open >=1)) return;
							open = open -1;
							p3 =0;
						}
						else
						{
							if (nondet_int())
							{
								if (!(p4 >=0)) return;
								if (!(p4 <=0)) return;
								if (!(barber >=1)) return;
								barber= barber-1;
								chair = chair +1;
								p4 = p4+1;
							}
							else
							{
								if (nondet_int())
								{
									if (! (p4 >=1)) return;
									if (! (p4 <=1)) return;
									if (! (open >=1)) return;
									open = open - 1;
									p4=p4 -1;
								}
								else
								{
									if (nondet_int())
									{
										if (! (p5>=0)) return;
										if (! (p5<=0)) return;
										barber=barber+1;
										p5=1;
									}
									else
									{
										if (nondet_int())
										{
											if (! (p5>=1)) return;
											if (! (p5<=1)) return;
											if (! (chair >=1)) return;
											chair= chair -1;
											p5=2;
										}
										else
										{
											if (nondet_int())
											{
												if (! (p5>=2)) return;
												if (! (p5<=2)) return;
												open=open +1;
												p5=3;
											}
											else
											{
												if (nondet_int())
												{
													if (! (p5 >= 3)) return;
													if (! (p5 <= 3)) return;
													if (! (open == 0)) return;
													p5=0;
												}
													else
												{
													if (! (p1 >= 1)) return;
													if (! (p1 <= 1)) return;
													if (! (open >= 1)) return;
													open = open-1;
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
	__VERIFIER_assert(p5 <= 3);
	__VERIFIER_assert(p5 >= open);
}

