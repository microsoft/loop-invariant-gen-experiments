int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 6;
  int junk_2 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_1 - (junk_0);
      x = y;
      junk_2 = junk_0 + (362);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_1 + (466);
      x = y;
      junk_2 = 96;
      y = ((y) + (1));
      junk_1 = junk_2 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
