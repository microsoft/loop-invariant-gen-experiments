void main() {
   int x, y;

   x = 0;
   y = 50;

  while( x < 100 ) {
    if( x < 50 ) {
      x = x+1;
    } else {
      x = x+1;
      y = y+1;
    }
  }

  if( y > 100 || y < 100 )
    goto ERROR;

  return;

ERROR: __VERIFIER_error();

}
