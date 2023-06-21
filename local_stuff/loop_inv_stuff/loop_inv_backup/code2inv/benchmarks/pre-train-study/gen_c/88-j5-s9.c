int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 0;
  int junk_3 = 8;
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
      junk_2 = junk_4;
      x = y;
      junk_0 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_0 - (junk_0);
      x = y;
      junk_1 = junk_4 - (700);
      y = ((y) + (1));
      junk_3 = 59 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
