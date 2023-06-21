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

	while(unknown())
	{
		if (unknown())
		{
			if (! (Eb >=1)) return;
			Eb = Eb -1;
			Mb = Mb +1;
		}
		else
		{
			if (unknown())
			{
				if (! (Ea >=1)) return;
				Ea = Ea -1;
				Ma = Ma +1;
			}
			else
			{
				if (unknown())
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
					if (unknown())
					{
						if (! (Sb>=1)) return;
						I=I+Sb+Eb+Mb;
						Sb=0;
						Eb=1;
						Mb=0;
					}
					else
					{
						if (unknown())
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
							if (unknown())
							{
								if (! (Sa>=1)) return;
								I=I+Sa+Ea+Ma;
								Sa=0;
								Ea=1;
								Ma=0;
							}
							else
							{
								if (unknown())
								{
									if (! (Sa>=1)) return;
									Sa=Sa-1;
									Sb=Sb+Eb+Mb+1;
									Eb=0;
									Mb=0;
								}
								else
								{
									if (unknown())
									{
										if (! (I>=1)) return;
										I=I-1;
										Sb=Sb+Eb+Mb+1;
										Eb=0;
										Mb=0;
									}
									else
									{
										if (unknown())
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

	assert(Ea + Ma <= 1);
	assert(Eb + Mb <= 1);
	assert(I >= 0);
	assert(Sa >= 0);
	assert(Ma  >= 0);
	assert(Ea  >= 0);
	assert(Sb >= 0);
	assert(Mb  >= 0);
	assert(Eb  >= 0);
	assert(I + Sa + Ea + Ma + Sb + Eb + Mb >= 1);
}


