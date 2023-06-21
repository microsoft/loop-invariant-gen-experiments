int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 0;
  int junk_3 = 0;
  int junk_4 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 544;
      x = y;
      junk_4 = junk_4 - (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_4;
      x = y;
      junk_0 = 845 + (junk_2);
      y = ((y) + (1));
      junk_3 = 862 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
