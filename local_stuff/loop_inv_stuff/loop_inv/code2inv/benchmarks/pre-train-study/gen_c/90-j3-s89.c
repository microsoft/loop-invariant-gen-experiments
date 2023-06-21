int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 1;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1 - (junk_2);
      x = y;
      junk_2 = junk_0 + (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 749;
      x = y;
      junk_0 = junk_0;
      y = ((y) + (1));
      junk_2 = 167 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
