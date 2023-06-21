int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 8;
  int junk_3 = 6;
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
    junk_4 = junk_3;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 425;
      y = ((y) + (2));
      junk_0 = junk_4 - (30);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_4 = junk_3 + (153);
      y = ((y) + (1));
      junk_3 = 972;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
