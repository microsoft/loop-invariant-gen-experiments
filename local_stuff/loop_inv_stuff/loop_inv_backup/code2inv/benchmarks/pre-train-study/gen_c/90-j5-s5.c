int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 6;
  int junk_2 = 6;
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
      junk_0 = junk_0;
      x = y;
      junk_4 = junk_1;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_3;
      x = y;
      junk_1 = 317 + (junk_2);
      y = ((y) + (1));
      junk_3 = 140;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
