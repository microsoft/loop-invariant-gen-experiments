int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 7;
  int junk_2 = 3;
  int junk_3 = 2;
  int junk_4 = 6;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 952;
      x = y;
      junk_3 = 198;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1;
      x = y;
      junk_4 = junk_4;
      y = ((y) + (1));
      junk_0 = 27;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
