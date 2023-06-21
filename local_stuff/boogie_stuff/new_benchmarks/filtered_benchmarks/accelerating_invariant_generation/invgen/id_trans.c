int main()
{
  int idBitLength, material_length, nlen;
  int j, k;
  assume(nlen == idBitLength / 32);

  j = 0;
  while((j < idBitLength / 8) && (j < material_length))
  {
    assert(0 <= j);
    assert(j < material_length);
    assert(0 <= j / 4);
    assert(j / 4 < nlen);
    j++;
  }
}
