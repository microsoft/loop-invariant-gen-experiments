int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 3;
  int junk_3 = 8;
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
    junk_0 = 639;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = junk_4;
      y = ((y) + (2));
      junk_1 = 669 - (junk_0);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = 334;
      y = ((y) + (1));
      junk_0 = 318;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
