int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 9;
  int junk_2 = 8;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_0;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_1 = 443 - (181);
      y = ((y) + (2));
      junk_2 = 562 - (junk_0);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = junk_2 + (junk_0);
      y = ((y) + (1));
      junk_2 = 164;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
