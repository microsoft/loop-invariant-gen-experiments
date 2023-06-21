int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 6;
  int junk_2 = 9;
  int junk_3 = 6;
  int junk_4 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 444;
      x = y;
      junk_4 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 + (junk_1);
      x = y;
      junk_4 = 560;
      y = ((y) + (1));
      junk_2 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
