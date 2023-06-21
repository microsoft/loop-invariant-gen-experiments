int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 9;
  int junk_3 = 1;
  int junk_4 = 6;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = junk_1;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = 904 + (junk_0);
      y = ((y) + (2));
      junk_2 = 398;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_2 = 5 + (junk_2);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
