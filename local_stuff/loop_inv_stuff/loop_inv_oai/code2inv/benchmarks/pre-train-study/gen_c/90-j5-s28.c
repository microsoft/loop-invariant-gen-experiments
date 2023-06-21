int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 2;
  int junk_2 = 0;
  int junk_3 = 1;
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
      junk_2 = junk_3;
      x = y;
      junk_1 = junk_2 - (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 878;
      x = y;
      junk_0 = 83;
      y = ((y) + (1));
      junk_2 = junk_3 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
