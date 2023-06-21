int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 6;
  int junk_3 = 6;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_1 + (junk_0);
      x = y;
      junk_1 = junk_2 - (junk_4);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 310 + (561);
      x = y;
      junk_0 = 184;
      y = ((y) + (1));
      junk_4 = junk_4 + (143);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
