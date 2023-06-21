int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 9;
  int junk_2 = 5;
  int junk_3 = 3;
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
      junk_3 = 408 + (678);
      x = y;
      junk_1 = 679;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_0;
      x = y;
      junk_2 = junk_0;
      y = ((y) + (1));
      junk_3 = junk_3 + (junk_3);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
