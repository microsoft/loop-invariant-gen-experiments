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
    junk_0 = 78;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = 816;
      y = ((y) + (2));
      junk_0 = junk_0 + (429);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 195 - (128);
      y = ((y) + (1));
      junk_0 = 851;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
