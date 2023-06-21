int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 2;
  int junk_2 = 0;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = 262 - (junk_0);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 557;
      y = ((y) + (2));
      junk_2 = 173;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = junk_2 + (junk_1);
      y = ((y) + (1));
      junk_1 = 417 + (junk_0);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
