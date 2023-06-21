int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 0;
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
    junk_2 = 907;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = junk_3 - (181);
      y = ((y) + (2));
      junk_4 = junk_2;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = junk_1;
      y = ((y) + (1));
      junk_2 = 842;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
