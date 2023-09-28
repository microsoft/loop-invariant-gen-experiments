#include "myassert.h"

/* Example where DAGGER is exponentially better thab SLAM, BLAST, SATABS */
int nondet_int();

int main () {
int x=0;

if (nondet_int()) x = x+1;
else x = x+22; 

if (nondet_int()) x = x+1;
else x = x+20; 

if (nondet_int()) x = x+1;
else x = x+18; 

if (nondet_int()) x = x+1;
else x = x+16; 

if (nondet_int()) x = x+1;
else x = x+14; 

if (nondet_int()) x = x+1;
else x = x+12; 

if (nondet_int()) x = x+1;
else x = x+10; 

if (nondet_int()) x = x+1;
else x = x+8; 

if (nondet_int()) x = x+1;
else x = x+6; 

if (nondet_int()) x = x+1;
else x = x+4; 

if (nondet_int()) x = x+1;
else x = x+2; 

__VERIFIER_assert(x <= 132);

return 0;
}
