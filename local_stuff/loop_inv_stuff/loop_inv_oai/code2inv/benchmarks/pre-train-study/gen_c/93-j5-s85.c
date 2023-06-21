int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 0;
  int junk_2 = 0;
  int junk_3 = 1;
  int junk_4 = 6;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = junk_2;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = 889 + (junk_2);
      y = ((y) + (2));
      junk_4 = 7;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = 284 - (junk_0);
      y = ((y) + (1));
      junk_2 = 374 - (junk_4);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
