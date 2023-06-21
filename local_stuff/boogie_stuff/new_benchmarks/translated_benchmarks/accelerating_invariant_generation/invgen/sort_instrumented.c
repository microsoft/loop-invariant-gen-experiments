int main()
{
  int heap_size, k_buffer, k_c;
  int n;
  n = unknown_int();
  int k;
  assume(n > 0);
  heap_size = 0;
  while (unknown())
  {
    k_buffer = 0;
    k = 0;
    while (k < n)
    {
      k_buffer++;
      heap_size++;
      k++;
    }

    k_c = k_buffer;
    while (unknown())
    {
      assume(k_c > 0);
      k_c--;
      heap_size--;
    }
    assume(k_c == 0);
  }
}