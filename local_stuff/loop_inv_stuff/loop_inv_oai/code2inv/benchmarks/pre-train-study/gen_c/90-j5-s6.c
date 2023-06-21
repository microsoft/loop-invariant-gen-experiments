int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 5;
  int junk_2 = 2;
  int junk_3 = 8;
  int junk_4 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0 + (junk_3);
      x = y;
      junk_4 = 637 + (351);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 788;
      x = y;
      junk_3 = 327;
      y = ((y) + (1));
      junk_4 = junk_4;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
