int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 1;
  int junk_2 = 8;
  int junk_3 = 4;
  int junk_4 = 3;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_4;
      x = y;
      junk_1 = 814 - (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1;
      x = y;
      junk_2 = 194;
      y = ((y) + (1));
      junk_4 = 623;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
