int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 0;
  int junk_4 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_3 - (877);
      x = y;
      junk_4 = 390 - (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 915;
      x = y;
      junk_4 = 783;
      y = ((y) + (1));
      junk_1 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
