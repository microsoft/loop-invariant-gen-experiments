int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
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
      junk_0 = 619 - (junk_0);
      y = ((y) + (2));
      junk_0 = 253;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 495 + (junk_0);
      y = ((y) + (1));
      junk_0 = 732 + (760);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
