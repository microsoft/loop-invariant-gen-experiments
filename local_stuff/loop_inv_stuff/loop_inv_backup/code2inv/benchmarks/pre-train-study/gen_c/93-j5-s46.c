int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 4;
  int junk_2 = 8;
  int junk_3 = 4;
  int junk_4 = 7;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = 917;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = junk_0 - (junk_1);
      y = ((y) + (2));
      junk_3 = 879 + (junk_4);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = junk_4 + (805);
      y = ((y) + (1));
      junk_2 = junk_3 - (junk_0);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
