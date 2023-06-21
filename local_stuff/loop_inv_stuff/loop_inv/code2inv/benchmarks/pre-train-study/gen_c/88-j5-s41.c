int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 6;
  int junk_2 = 0;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 185 - (junk_2);
      x = y;
      junk_0 = 218 - (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_2 + (884);
      x = y;
      junk_4 = junk_1;
      y = ((y) + (1));
      junk_1 = junk_2 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
