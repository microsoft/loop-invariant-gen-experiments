#include "seahorn/seahorn.h"

extern int unknown();

void main()
{
  int tagbuf_len = unknown();
  int t;
  //int __BLAST_NONDET;

  //tmpl("(le(tagbuf_len, t), le(tagbuf_len, t))");
  //  tmpl("le(tagbuf_len, t)");
  
  if(tagbuf_len >= 1); else goto END;

  t = 0;

  --tagbuf_len;
  /*
  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));
  */

  /*
  if (c == '-') {
    GET_CHAR(c, NULL);
    if (c == '-') {
      do {
        GET_CHAR(c, NULL);
      } while (ap_isspace(c));
      if (c == '>') {
        ap_cpystrn(tag, "done", tagbuf_len);
        return tag;
      }
    }
    return NULL;
  }
  */

  while (1) {
    if (t == tagbuf_len) {
      sassert(0 <= t);
      sassert(t <= tagbuf_len);
      //      tag[t] = EOS;
      goto END;
    }
    if (unknown()) {
      break;
    }
     sassert(0 <= t);
     sassert(t <= tagbuf_len);
    //    tag[t] = ap_tolower(c);
    t++;
    //    GET_CHAR(c, NULL);
  }

   sassert(0 <= t);
   sassert(t <= tagbuf_len);
  //  tag[t] = EOS;
  t++;
  //  tag_val = tag + t;
  /*
  while (ap_isspace(c)) {
    GET_CHAR(c, NULL);
  }
  if (c != '=') {
    return NULL;
  }

  do {
    GET_CHAR(c, NULL);
  } while (ap_isspace(c));

  if (c != '"' && c != '\'') {
    return NULL;
  }
  term = c;
  */
  while (1) {
    //    GET_CHAR(c, NULL);
    if (t == tagbuf_len) { /* Suppose t == tagbuf_len - 1 */
      sassert(0 <= t);
      sassert(t <= tagbuf_len);
      //      tag[t] = EOS;
      goto END;
    }

    if (unknown()) {
      //      GET_CHAR(c, NULL);
      if ( unknown()) {
        /* OK */
	 sassert(0 <= t);
	sassert(t <= tagbuf_len); // interesting assert, t2.
	//        tag[t] = '\\';
        t++;
        if (t == tagbuf_len) {
          /* OK */
	  sassert(0 <= t);
	  sassert(t <= tagbuf_len);
	  //          tag[t] = EOS;
          goto END;
        }
      }
    }
    else if ( unknown()) {
      break;
    }

    /* OK */
    sassert(0 <= t);
    sassert(t <= tagbuf_len);
    //    tag[t] = c;    
    t++;                /* Now t == tagbuf_len + 1 
                         * So the bounds check (t == tagbuf_len) will fail */
  }
  /* OK */ 
  sassert(0 <= t);
  sassert(t <= tagbuf_len);
  //  tag[t] = EOS;

  END:;
}
