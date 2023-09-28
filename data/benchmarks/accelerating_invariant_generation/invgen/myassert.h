assume(int cond)
{
  __VERIFIER_assume(cond);
}

__VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

