#include "myassert.h"

int nondet_int();

//This example is adapted from StInG 
int main()
{
	int I;
	int Sa;
	int Ea;
	int Ma;
	int Sb;
	int Eb;
	int Mb;

	if (! (I>=1)) return;
	Sa=0;
	Ea=0;
	Ma=0;
	Sb=0;
	Eb=0;
	Mb=0;

	while(nondet_int())
	{
		if (nondet_int())
		{
			if (! (Eb >=1)) return;
			Eb = Eb -1;
			Mb = Mb +1;
		}
		else
		{
			if (nondet_int())
			{
				if (! (Ea >=1)) return;
				Ea = Ea -1;
				Ma = Ma +1;
			}
			else
			{
				if (nondet_int())
				{
					if (! (Sa>=1)) return;
					Sa=Sa-1;
					I=I+Sb+Eb+Mb;
					Sb=0;
					Eb=1;
					Mb=0;

				}
				else
				{
					if (nondet_int())
					{
						if (! (Sb>=1)) return;
						I=I+Sb+Eb+Mb;
						Sb=0;
						Eb=1;
						Mb=0;
					}
					else
					{
						if (nondet_int())
						{

							if (! (Sb>=1)) return;
							Sb=Sb-1;
							I=I+Sa+Ea+Ma;
							Sa=0;
							Ea=1;
							Ma=0;

						}
						else
						{
							if (nondet_int())
							{
								if (! (Sa>=1)) return;
								I=I+Sa+Ea+Ma;
								Sa=0;
								Ea=1;
								Ma=0;
							}
							else
							{
								if (nondet_int())
								{
									if (! (Sa>=1)) return;
									Sa=Sa-1;
									Sb=Sb+Eb+Mb+1;
									Eb=0;
									Mb=0;
								}
								else
								{
									if (nondet_int())
									{
										if (! (I>=1)) return;
										I=I-1;
										Sb=Sb+Eb+Mb+1;
										Eb=0;
										Mb=0;
									}
									else
									{
										if (nondet_int())
										{
											if (! (I >= 1)) return;
											I = I -1;
											Sa = Sa + Ea + Ma + 1;
											Ea = 0;
											Ma =0;
										}
										else
										{
											if (! (Sb >= 1)) return;
											Sb = Sb-1;
											Sa = Ea+Ma+1;
											Ea = 0;
											Ma = 0;

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

	__VERIFIER_assert(Ea + Ma <= 1);
	__VERIFIER_assert(Eb + Mb <= 1);
	__VERIFIER_assert(I + Sa + Ea + Ma + Sb + Eb + Mb >= 1);
}

