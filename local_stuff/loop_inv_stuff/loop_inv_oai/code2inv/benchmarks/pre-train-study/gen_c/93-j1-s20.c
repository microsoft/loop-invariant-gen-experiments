int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = 38;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 445;
      y = ((y) + (2));
      junk_0 = 125 - (junk_0);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 186;
      y = ((y) + (1));
      junk_0 = 829 + (795);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
