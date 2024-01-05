#include "myassert.h"

int __BLAST_NONDET;


int main ()
{
  //  int pathbuf[MAXPATHLEN+1];

  int MAXPATHLEN;
  int pathbuf_off;

  /* Char *bound = pathbuf + sizeof(pathbuf)/sizeof(*pathbuf) - 1; */
  int bound_off;

  /* glob2's local vars */
  /* Char *p; */
  int glob2_p_off;
  int glob2_pathbuf_off;
  int glob2_pathlim_off;

  if(MAXPATHLEN > 0); else goto END;

  pathbuf_off = 0;
  bound_off = pathbuf_off + (MAXPATHLEN + 1) - 1;

  /* glob2 (pathbuf, bound); */

  /*
int glob2 (Char *pathbuf, Char *pathlim)
{
*/

  glob2_pathbuf_off = pathbuf_off;
  glob2_pathlim_off = bound_off;

  for (glob2_p_off = glob2_pathbuf_off;
      glob2_p_off <= glob2_pathlim_off;
      glob2_p_off++) {
    /* OK */
    /* *p = 1; */
    __VERIFIER_assert(0 <= glob2_p_off ); __VERIFIER_assert(glob2_p_off < MAXPATHLEN + 1);
    //pathbuf[glob2_p_off] = 1;
  }

  /*
  return 0;
}
*/

 END:  return 0;
}
