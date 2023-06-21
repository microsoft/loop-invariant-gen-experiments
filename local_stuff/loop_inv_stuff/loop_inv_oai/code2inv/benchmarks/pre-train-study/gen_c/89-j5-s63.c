int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 0;
  int junk_2 = 0;
  int junk_3 = 7;
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
      junk_1 = junk_3;
      x = y;
      junk_4 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 943 + (840);
      x = y;
      junk_3 = 147 + (junk_3);
      y = ((y) + (1));
      junk_4 = junk_0 - (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
