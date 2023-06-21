int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 928 - (junk_1);
      x = y;
      junk_3 = 570 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = junk_4;
      x = y;
      junk_4 = 955 - (junk_3);
      y = ((y) + (1));
      junk_2 = junk_3 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
