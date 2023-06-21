int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 6;
  int junk_3 = 1;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_4 + (junk_0);
      x = y;
      junk_0 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 713 + (junk_2);
      x = y;
      junk_1 = 405;
      y = ((y) + (1));
      junk_3 = junk_0 - (916);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
