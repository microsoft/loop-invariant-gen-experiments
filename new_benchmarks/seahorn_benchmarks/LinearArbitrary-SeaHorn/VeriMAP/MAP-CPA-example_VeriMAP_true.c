int main() {
  int i = 0;
  int a = 0;

  while (1) {
    if (i == 20) {
       goto LOOPEND;
    } else {
       i++;
       a++;
    }

    if (i != a) {
      goto ERROR;
    }
  }

  LOOPEND:

  if (a != 20) {
     goto ERROR;
  }

  return (0);
  ERROR: __VERIFIER_error();
  return (-1);
}

