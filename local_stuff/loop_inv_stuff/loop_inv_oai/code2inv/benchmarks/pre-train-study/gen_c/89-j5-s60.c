int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 4;
  int junk_3 = 3;
  int junk_4 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 27;
      x = y;
      junk_3 = 116 - (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 940;
      x = y;
      junk_0 = junk_0;
      y = ((y) + (1));
      junk_3 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
