
__VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

#define __VERIFIER_assert(cond) sassert(cond)