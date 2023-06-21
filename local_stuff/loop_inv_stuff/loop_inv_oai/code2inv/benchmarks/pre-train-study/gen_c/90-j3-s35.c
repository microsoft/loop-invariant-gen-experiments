int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_0 - (188);
      x = y;
      junk_1 = junk_1 + (387);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 165 - (junk_0);
      x = y;
      junk_2 = junk_0;
      y = ((y) + (1));
      junk_1 = junk_0 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
