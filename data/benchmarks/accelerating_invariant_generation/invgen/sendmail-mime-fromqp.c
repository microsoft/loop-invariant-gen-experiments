#include "myassert.h"

int __BLAST_NONDET;

int main (void)
{
  int outfilelen;
  //  char outfile[BASE_SZ]; // originally MAXLINE
    // originally a function argument **ooutfile; this function modified
    // caller's pointer into outbut buffer

  //int c1, c2;

  // number of chars copied from infile into outfile; reset when
  // continuation sequence "=\n" is read
  int nchar = 0;

  int out = 0; // index into outfile

  tmpl("(le(nchar,out,outfilelen),le(nchar,out,outfilelen),le(nchar,out,outfilelen))");

  if(outfilelen > 0); else goto RETURN;

  //  while ((c1 = nondet_char ()) != EOS)
  while(__BLAST_NONDET)
  {
    //    if (c1 == '=')
    if(__BLAST_NONDET)
    {
      // malformed: early EOS
      //      if ((c1 = nondet_char ()) == EOS)
      if(__BLAST_NONDET)
	// in Zitser, these breaks actually return to the caller where the
	// pointer into outfile is reset before this is called again
	goto AFTERLOOP; 

      // =\n: continuation; signal to caller it's ok to pass in more infile
      // OK: reset out before taking more input
      //if (c1 == '\n')
      if(__BLAST_NONDET)
      {
	out = 0;
	nchar = 0;
	goto LOOPEND;
      }
      else
      {
	// convert, e.g., "=5c" to int

	// malformed: early EOF
	//if ((c2 = nondet_char ()) == EOS)
	if(__BLAST_NONDET)  goto AFTERLOOP;

	nchar++;
	if (nchar >= outfilelen)
	  goto AFTERLOOP;

	/* OK */
	__VERIFIER_assert(0<=out);//1
	__VERIFIER_assert(out<outfilelen);//2
	// outfile[out] = c1;
	out++;
      }
    }
    else
    {
      // regular character, copy verbatim

      nchar++;
      if (nchar >= outfilelen)
	goto AFTERLOOP;

      /* OK */
      __VERIFIER_assert(0<=out);//3
      __VERIFIER_assert(out<outfilelen);//4
      //  outfile[out] = c1;
      out++;

      //if (c1 == '\n')
      if(__BLAST_NONDET) goto AFTERLOOP;
    }
  LOOPEND:;
  }
 AFTERLOOP:

  /* OK */
  __VERIFIER_assert(0<=out);//5
  __VERIFIER_assert(out<outfilelen);
  //  outfile[out] = EOS;
  out++;
 RETURN:  return 0;
}
