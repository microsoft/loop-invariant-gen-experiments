int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 0;
  int junk_2 = 0;
  int junk_3 = 8;
  int junk_4 = 1;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_4 = 816;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = junk_1 + (429);
      y = ((y) + (2));
      junk_1 = 195 - (128);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = 851;
      y = ((y) + (1));
      junk_2 = 62;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
