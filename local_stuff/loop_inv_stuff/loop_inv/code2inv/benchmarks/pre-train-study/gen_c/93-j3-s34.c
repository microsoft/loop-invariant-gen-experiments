int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 4;
  int junk_2 = 6;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = junk_2;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_1 = junk_2;
      y = ((y) + (2));
      junk_2 = junk_1;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = 132;
      y = ((y) + (1));
      junk_0 = 79;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
