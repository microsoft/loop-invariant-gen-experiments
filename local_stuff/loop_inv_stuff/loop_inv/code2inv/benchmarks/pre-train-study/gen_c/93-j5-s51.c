int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 2;
  int junk_2 = 1;
  int junk_3 = 1;
  int junk_4 = 4;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_4 = junk_2 - (junk_1);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 396;
      y = ((y) + (2));
      junk_4 = junk_2 - (142);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_0 = junk_4 - (474);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
