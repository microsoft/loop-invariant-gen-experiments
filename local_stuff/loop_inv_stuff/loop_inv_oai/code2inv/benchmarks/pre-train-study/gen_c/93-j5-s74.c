int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 8;
  int junk_2 = 1;
  int junk_3 = 4;
  int junk_4 = 2;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = junk_1;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = 3 - (junk_1);
      y = ((y) + (2));
      junk_3 = 474 - (junk_2);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = 56;
      y = ((y) + (1));
      junk_2 = 175 + (769);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
