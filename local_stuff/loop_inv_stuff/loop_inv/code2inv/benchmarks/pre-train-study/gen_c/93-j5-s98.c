int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 6;
  int junk_3 = 1;
  int junk_4 = 3;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_4 = 380;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = junk_4;
      y = ((y) + (2));
      junk_4 = junk_0 - (junk_4);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = junk_0 + (26);
      y = ((y) + (1));
      junk_1 = 63 - (junk_2);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
