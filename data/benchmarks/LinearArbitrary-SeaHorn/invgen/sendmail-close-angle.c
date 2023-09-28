/*
 * Variant: This one just blindly copies the input into buffer and writes '>''\0' at the end.
 */

#include "seahorn/seahorn.h"

extern int unknown();


int main (void)
{
  //  char buffer[BASE_SZ+1];
  //  char input[BASE_SZ+70];
  //  char *buf;
  //  char *buflim;
  //  char *in;
  //  char cur;
  //int __BLAST_NONDET;
  int in;
  int inlen = unknown();
  int bufferlen = unknown();
  int buf;
  int buflim;

  //tmpl("(le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim))");
  //tmpl("(le(in,inlen,buf,bufferlen,buflim),le(in,inlen,buf,bufferlen,buflim))");
  
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
  // assert(0<=in);
  // assert(in<inlen);
  while (unknown())
  {
    if (buf == buflim)
      break;
    sassert(0<=buf);
    sassert(buf<bufferlen); 
    //*buf = cur;
    buf++;
out:
    in++;
    sassert(0<=in);//3
    sassert(in<inlen);//4
    //cur = *in;
  }

    sassert(0<=buf);//5
    sassert(buf<bufferlen);//5
  //*buf = '>';
  buf++;

  /* OK */
  sassert(0<=buf);//6
  sassert(buf<bufferlen);

  //  *buf = EOS;
  buf++;

 END:  return 0;
}
