#include "myassert.h"

int __BLAST_NONDET;

int main ()
{
  /*
  Char *buf;
  Char *pattern;
  Char *bound;
  */
  int buf_off, pattern_off, bound_off;

  int MAXPATHLEN;
  //  int A [MAXPATHLEN+1];
  //  int B [PATTERNLEN];

  /* glob3's locals */
  // char d_name[MAXNAMLEN + 1];
  int error;
  // char g3_buf[MAXPATHLEN];
  int pathbuf_off;
  int pathend_off;
  int pathlim_off;

  /*
  buf = A;
  pattern = B;
  */
  if(MAXPATHLEN >0); else goto END;

  buf_off = 0;
  pattern_off = 0;

  bound_off = MAXPATHLEN;

/*  glob3 (
 *  	buf,
 *  	buf,
 *  	bound,
 *  	pattern);

static int
glob3(
	Char *pathbuf,
	Char *pathend,
	Char *pathlim,
	Char *pattern)
*/
  pathbuf_off = 0;
  pathend_off = 0;
  pathlim_off = MAXPATHLEN;

  //  A[pathend_off] = EOS;
	    
  error = 0;

  /* LOOP */
  while (__BLAST_NONDET) {
    int i;

    /* Initial DOT must be matched literally. */
    __VERIFIER_assert(0 <= pattern_off ); __VERIFIER_assert( pattern_off <= MAXPATHLEN);
    //if (d_name[0] == DOT && B[pattern_off] != DOT)
      if (__BLAST_NONDET) continue;
    /*
     * The resulting string contains EOS, so we can
     * use the pathlim character, if it is the nul
     */
    i = 0;
    for (;;) 
      if (i > MAXPATHLEN) goto END;
      else {
	__VERIFIER_assert(0 <= i);	__VERIFIER_assert( i <= MAXPATHLEN);
        //A[i] = d_name[i];
        i++;
        if (__BLAST_NONDET) goto END;
      }

    /*
     * Have we filled the buffer without seeing EOS?
     */
    __VERIFIER_assert(0 <= pathlim_off ); __VERIFIER_assert( pathlim_off <= MAXPATHLEN);

    //    if (i > MAXPATHLEN && B[pathlim_off] != EOS) 
    if (i > MAXPATHLEN){
      if ( __BLAST_NONDET ) {
	/*
	 * Abort when requested by caller, otherwise
	 * reset pathend back to last SEP and continue
	 * with next dir entry.
	 */
	if ( __BLAST_NONDET ) {
	  error = 5;
	  goto END;
	}
	else {
	  /* OK */
	  __VERIFIER_assert(0 <= i);__VERIFIER_assert(i <= MAXPATHLEN + 1);
	  //A[i] = EOS;
	  continue;
	}
      }
    }
    /* match() is scary, and recursive, which Satabs can't handle.
     * Replacing it with a non-deterministic stub....
     *
     * This is irrelevant to overflow detection anyhow, since this 
     * is *after* the overflow. */
    if (/*!match(pathend, pattern, restpattern)*/__BLAST_NONDET) {
      /* OK */
      __VERIFIER_assert(i <= MAXPATHLEN + 1);
      //A[i] = EOS;
      continue;
    }
  END_LOOP1:;
  }

  /* end glob3 */

 END:  return 0;
}
