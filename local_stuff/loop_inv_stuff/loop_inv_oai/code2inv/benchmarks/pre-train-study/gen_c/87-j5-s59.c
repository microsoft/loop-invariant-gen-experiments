int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 1;
  int junk_3 = 7;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_4;
      x = y;
      junk_3 = 649;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 770;
      x = y;
      junk_1 = junk_4;
      y = ((y) + (1));
      junk_4 = junk_3 + (junk_3);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
