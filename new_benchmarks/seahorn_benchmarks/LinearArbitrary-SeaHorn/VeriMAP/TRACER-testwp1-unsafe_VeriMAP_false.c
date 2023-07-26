extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp1.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp1.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testwp1.tmp.c"
main()
{
  int x, y, z;

        if (x>0)
          z = 2;
        else
          x = -1;


        if (y>0)

          z = 3;
        else

          y = 1;

  __VERIFIER_assert(!( x+y<=0 ));
}
