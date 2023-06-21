int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 7;
  int junk_2 = 7;
  int junk_3 = 1;
  int junk_4 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 67 + (junk_0);
      x = y;
      junk_2 = junk_0 + (839);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_2;
      x = y;
      junk_1 = junk_2;
      y = ((y) + (1));
      junk_2 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
