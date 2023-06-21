int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = junk_0;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = junk_0;
      y = ((y) + (2));
      junk_0 = junk_0 - (399);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 21;
      y = ((y) + (1));
      junk_0 = junk_0 - (762);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
