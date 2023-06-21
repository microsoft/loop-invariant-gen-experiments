int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 3;
  int junk_2 = 4;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_2;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_1 = junk_2 + (196);
      y = ((y) + (2));
      junk_2 = 865;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = junk_1 + (junk_2);
      y = ((y) + (1));
      junk_1 = junk_1;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
