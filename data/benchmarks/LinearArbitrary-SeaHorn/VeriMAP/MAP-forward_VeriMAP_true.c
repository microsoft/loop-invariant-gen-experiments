void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
int __VERIFIER_nondet_int(){int x; return x;}
void main(){

   int i, n, a, b;
   n = __VERIFIER_nondet_int();
   __VERIFIER_assume( n>= 0 );

   i = 0; 
   a = 0; 
   b = 0;

   while( i < n ){
      if(__VERIFIER_nondet_int()) {
         a = a+1;
         b = b+2;
      } else {
         a = a+2;
         b = b+1;
      }
      i = i+1;
   }

   if ( a+b != 3*n)
      goto ERROR;

return;

ERROR:__VERIFIER_error();
}
