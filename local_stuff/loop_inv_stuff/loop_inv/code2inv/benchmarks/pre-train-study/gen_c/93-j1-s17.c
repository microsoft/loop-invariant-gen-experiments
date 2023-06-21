int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = 841;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 847;
      y = ((y) + (2));
      junk_0 = 692 - (junk_0);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = junk_0 + (365);
      y = ((y) + (1));
      junk_0 = 938;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
