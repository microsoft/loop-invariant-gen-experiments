#include "seahorn/seahorn.h"

extern int unknown();

void main ()
{
  //int __BLAST_NONDET;
  int scheme = unknown();
  int urilen,tokenlen;
  urilen = unknown();
  tokenlen = unknown();
  int cp,c;
  //  char *token[TOKEN_SZ];

  tmpl("(le(scheme,urilen,tokenlen,cp,c),le(scheme,urilen,tokenlen,cp,c))");
  if(urilen>0); else goto END;
  if(tokenlen>0); else goto END;
  if(scheme >= 0 );else goto END;
  if (scheme == 0
      || (urilen-1 < scheme)) {
    goto END;
  }

  cp = scheme;
  
  sassert(cp-1 < urilen);
  sassert(0 <= cp-1);

  if (unknown()) {
    sassert(cp < urilen);
    sassert(0 <= cp);
    while ( cp != urilen-1) {
      if(unknown()) break;
      sassert(cp < urilen);
      sassert(0 <= cp);
      ++cp;
    }
    sassert(cp < urilen);
    sassert( 0 <= cp );
    if (cp == urilen-1) goto END;
    sassert(cp+1 < urilen);
    sassert( 0 <= cp+1 );
    if (cp+1 == urilen-1) goto END;
    ++cp;

    scheme = cp;

    if (unknown()) {
      c = 0;
      //token[0] = uri;
      sassert(cp < urilen);
      sassert(0<=cp);
      while ( cp != urilen-1
             && c < tokenlen - 1) {
	sassert(cp < urilen);
	sassert(0<=cp);
        if (unknown()) {
          ++c;
          /* OK */
	  sassert(c < tokenlen);
	  sassert(0<=c);
          //token[c] = uri + cp + 1;
	  sassert(cp < urilen); //Interesting assert
	  sassert(0<=cp);
          //uri[cp] = EOS;
        }
        ++cp;
      }
      goto END;
    }
  }

 END:;
}
