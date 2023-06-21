int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 0;
  int junk_2 = 1;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = junk_0 - (149);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = junk_1;
      y = ((y) + (2));
      junk_0 = junk_2 + (junk_1);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 615;
      y = ((y) + (1));
      junk_2 = junk_0 + (982);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
