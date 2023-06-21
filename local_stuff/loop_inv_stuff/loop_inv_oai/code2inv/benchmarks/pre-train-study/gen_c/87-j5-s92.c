int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 6;
  int junk_2 = 0;
  int junk_3 = 8;
  int junk_4 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 743 - (junk_1);
      x = y;
      junk_1 = junk_4 - (junk_0);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 201 + (752);
      x = y;
      junk_3 = 516;
      y = ((y) + (1));
      junk_4 = junk_2 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
