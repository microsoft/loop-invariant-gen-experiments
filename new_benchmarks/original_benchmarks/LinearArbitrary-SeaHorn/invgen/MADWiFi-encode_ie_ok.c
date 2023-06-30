#include "seahorn/seahorn.h"

extern int unknown();

int main()
{
  /* buf is treated as an array of unsigned 8-byte ints */
  //  u_int8_t *p;
  int p;
  int i;
  int leader_len = unknown();
  int bufsize = unknown();
  int bufsize_0 = unknown();
  int ielen = unknown();

  //tmpl("(le(p,i,leader_len,bufsize,bufsize_0,ielen),le(p,i,leader_len,bufsize,bufsize_0,ielen))");

  // copy the contents of leader into buf
  if(leader_len >0); else goto END;
  if(bufsize >0); else goto END;
  if(ielen >0); else goto END;

  if (bufsize < leader_len)
    goto END;

  //  p = buf;
  p = 0;
  //  memcpy(p, leader, leader_len);
  bufsize_0 = bufsize;
  bufsize -= leader_len;
  p += leader_len;

  /* This is the fix. */
  if (bufsize < 2*ielen)
    goto END;

  //  assert(p+ielen<=bufsize_0);

  for (i = 0; i < ielen && bufsize > 2; i++) {
    sassert(0<=p);
    sassert(p+1<bufsize_0);
      //    *p = 'x';
      //    *(p+1) = 'x';
    p += 2;
  }

  // if we wrote all of ie[], say how many bytes written in total, 
  // otherwise, claim we wrote nothing
  // return (i == ielen ? p - (u_int8_t *)buf : 0);
 END:;
}

