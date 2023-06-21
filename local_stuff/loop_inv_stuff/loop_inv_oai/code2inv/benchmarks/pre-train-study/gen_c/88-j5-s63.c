int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 5;
  int junk_2 = 1;
  int junk_3 = 0;
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
      junk_2 = junk_2;
      x = y;
      junk_1 = 990 - (118);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_3;
      x = y;
      junk_3 = junk_1;
      y = ((y) + (1));
      junk_1 = 904 + (291);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
