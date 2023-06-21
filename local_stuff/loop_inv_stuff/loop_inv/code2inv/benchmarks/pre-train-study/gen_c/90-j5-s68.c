int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 1;
  int junk_2 = 1;
  int junk_3 = 7;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_0;
      x = y;
      junk_2 = 924 - (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_2 + (624);
      x = y;
      junk_0 = 417 - (junk_0);
      y = ((y) + (1));
      junk_3 = 862 + (320);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
