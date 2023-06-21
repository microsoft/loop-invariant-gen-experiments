int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 7;
  int junk_3 = 1;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_0;
      x = y;
      junk_3 = 874 - (43);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 361;
      x = y;
      junk_2 = 35 - (junk_0);
      y = ((y) + (1));
      junk_1 = 43;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
