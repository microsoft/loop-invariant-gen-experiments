int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 9;
  int junk_2 = 8;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = junk_3;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = junk_1;
      y = ((y) + (2));
      junk_0 = junk_3 - (760);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 265 - (343);
      y = ((y) + (1));
      junk_2 = junk_1;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
