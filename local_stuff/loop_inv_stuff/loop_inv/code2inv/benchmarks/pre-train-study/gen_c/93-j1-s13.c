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
    junk_0 = 176;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 442 + (512);
      y = ((y) + (2));
      junk_0 = 692;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 808;
      y = ((y) + (1));
      junk_0 = 865;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
