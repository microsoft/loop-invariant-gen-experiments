int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 7;
  int junk_2 = 1;
  int junk_3 = 8;
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
      junk_2 = junk_0;
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 849;
      x = y;
      junk_1 = junk_3 - (621);
      y = ((y) + (1));
      junk_4 = junk_3 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
