int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 0;
  int junk_2 = 6;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = 591 + (junk_4);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = 566 - (junk_3);
      y = ((y) + (2));
      junk_3 = junk_4 + (junk_4);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = 695;
      y = ((y) + (1));
      junk_3 = junk_1 - (junk_1);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
