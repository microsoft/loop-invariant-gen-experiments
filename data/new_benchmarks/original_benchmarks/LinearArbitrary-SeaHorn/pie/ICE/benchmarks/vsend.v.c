void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
int main (void)
{
  char in[11]; // = "3277192070";
  char *s;
  unsigned char c;
  unsigned int i, j;
  int idx_in;
  int v1, v2, v3;
  in[10] = 0;
  idx_in = 0;
  s = in;
  i = 0;
  c = in[idx_in];
  while (('0' <= c) && (c <= '9'))
  {
    j = c - '0';
    i = i * 10 + j;
    idx_in++;
    c = in[idx_in];
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();
  }
  /* OK */
  __VERIFIER_assert (i >= 0);
  return 0;
}

