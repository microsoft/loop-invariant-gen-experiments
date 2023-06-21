int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 9;
  int junk_2 = 7;
  int junk_3 = 4;
  int junk_4 = 8;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_4 = junk_0 + (812);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = junk_1 + (junk_0);
      y = ((y) + (2));
      junk_4 = junk_4;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_4 = 925;
      y = ((y) + (1));
      junk_0 = junk_4;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
