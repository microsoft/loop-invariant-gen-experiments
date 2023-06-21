int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 7;
  int junk_2 = 1;
  int junk_3 = 9;
  int junk_4 = 7;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_1;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = 257;
      y = ((y) + (2));
      junk_0 = 879 - (769);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = 958;
      y = ((y) + (1));
      junk_1 = junk_3;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
