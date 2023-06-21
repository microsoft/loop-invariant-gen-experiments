int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 7;
  int junk_3 = 4;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 98 + (junk_3);
      x = y;
      junk_0 = 212 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_4 + (junk_0);
      x = y;
      junk_2 = junk_3;
      y = ((y) + (1));
      junk_4 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
