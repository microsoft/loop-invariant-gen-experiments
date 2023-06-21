int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 8;
  int junk_3 = 3;
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
      junk_4 = junk_2;
      x = y;
      junk_3 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 866;
      x = y;
      junk_2 = junk_3 + (junk_2);
      y = ((y) + (1));
      junk_1 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
