#include "myassert.h"

int main() {
  
  int cp1_off, n1, n2, mc_i;
  int MAXDATA;
  if (MAXDATA > 0 ); else goto END;

  if ((n1 <= MAXDATA * 2)); else goto END;

  if ((cp1_off <= n1)); else goto END;

  if ((n2 <= MAXDATA*2 - n1)); else goto END;

  for (mc_i = 0; mc_i < n2; mc_i++) {
    /* OK */
    __VERIFIER_assert(cp1_off+mc_i < MAXDATA * 2);
    // data[cp1_off+mc_i] = msg[cp_off+mc_i];
  }

  /* end of rrextract */

 END:  return 0;
}
