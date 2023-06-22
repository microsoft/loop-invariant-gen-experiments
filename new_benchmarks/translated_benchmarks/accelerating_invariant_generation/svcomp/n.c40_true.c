int main() {
  int x[100];
  int y[100];
  int i,j,k;
  k = unknown_int();
  i = 0;
  while(x[i] != 0){
    y[i] = x[i];
    i++;
  }
  y[i] = 0;
  assert(!((y[k] == 0) && (k >= 0 && k < i)));
}
