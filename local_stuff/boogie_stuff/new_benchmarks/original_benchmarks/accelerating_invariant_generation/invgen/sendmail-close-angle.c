/*
 * Variant: This one just blindly copies the input into buffer and writes '>''\0' at the end.
 */

#include "myassert.h"


int main (void)
{
  //  char buffer[BASE_SZ+1];
  //  char input[BASE_SZ+70];
  //  char *buf;
  //  char *buflim;
  //  char *in;
  //  char cur;
  int __BLAST_NONDET;
  int in;
  int inlen;
  int bufferlen;
  int buf;
  int buflim;

  //tmpl("(le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim))");
  tmpl("(le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim))");
  
  if(bufferlen >1);else goto END;
  if(inlen > 0);else goto END;
  if(bufferlen < inlen);else goto END;
//  shouldn't be necessary unless checking for safety of *in
//  input[BASE_SZ+70-1] = EOS;
//  in = input;
//  buf = buffer;
  buf = 0;
  in = 0;
  buflim = bufferlen - 2;
    // reserved enough space for both '>' and '\0'!
  // __VERIFIER_assert(0<=in);
  // __VERIFIER_assert(in<inlen);
  while (__BLAST_NONDET)
  {
    if (buf == buflim)
      break;
    __VERIFIER_assert(0<=buf);
    __VERIFIER_assert(buf<bufferlen); 
    //*buf = cur;
    buf++;
out:
    in++;
    __VERIFIER_assert(0<=in);//3
    __VERIFIER_assert(in<inlen);//4
    //cur = *in;
  }

    __VERIFIER_assert(0<=buf);//5
    __VERIFIER_assert(buf<bufferlen);//5
  //*buf = '>';
  buf++;

  /* OK */
  __VERIFIER_assert(0<=buf);//6
  __VERIFIER_assert(buf<bufferlen);

  //  *buf = EOS;
  buf++;

 END:  return 0;
}
