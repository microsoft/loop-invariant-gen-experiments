#include "myassert.h"

int main (void)
{
  //  char fbuf[MAXLINE+1];
  int __BLAST_NONDET;
  int fbuflen;
  int fb;
  //  int c1, c2, c3;
  tmpl("(le(fbuflen,fb),le(fbuflen,fb))");
  if(fbuflen >0);else goto END;
  fb = 0;
  while (__BLAST_NONDET)
  {
    //c2 = nondet_int ();
    if (__BLAST_NONDET)
      break;

    //c3 = nondet_int ();
    if (__BLAST_NONDET)
      break;

    /* OK */
    __VERIFIER_assert(0<=fb);
    __VERIFIER_assert(fb<fbuflen);
    //fbuf[fb] = c1;
    fb++;
    if (fb >= fbuflen-1)
      fb = 0;

    /* OK */
    __VERIFIER_assert(0<=fb);
    __VERIFIER_assert(fb<fbuflen);

    //    fbuf[fb] = c2;
    fb++;
    if (fb >= fbuflen-1)
      fb = 0;

    /* OK */
    __VERIFIER_assert(0<=fb);
    __VERIFIER_assert(fb<fbuflen);

    //    fbuf[fb] = c3;
    fb++;
    if (fb >= fbuflen-1)
      fb = 0;
  }

  /* force out partial last line */
  if (fb > 0)
  {
    /* OK */
    __VERIFIER_assert(0<=fb);
    __VERIFIER_assert(fb<fbuflen);
        //fbuf[fb] = EOS;
  }

 END:  return 0;
}
