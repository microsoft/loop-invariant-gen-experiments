int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 8;
  int junk_2 = 6;
  int junk_3 = 6;
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
      junk_3 = junk_1 - (469);
      x = y;
      junk_4 = junk_0 - (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 798;
      x = y;
      junk_3 = junk_0 + (97);
      y = ((y) + (1));
      junk_1 = junk_3 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
