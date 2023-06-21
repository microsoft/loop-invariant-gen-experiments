int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 0;
  int junk_2 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_2;
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 507;
      x = y;
      junk_1 = 568;
      y = ((y) + (1));
      junk_0 = 766 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
