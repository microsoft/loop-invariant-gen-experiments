int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 1;
  int junk_2 = 4;
  int junk_3 = 5;
  int junk_4 = 4;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = 740;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = 415;
      y = ((y) + (2));
      junk_3 = junk_3;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = 513;
      y = ((y) + (1));
      junk_0 = 352 + (junk_1);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
