int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 8;
  int junk_3 = 5;
  int junk_4 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_3;
      x = y;
      junk_1 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_1 = junk_2 - (junk_3);
      y = ((y) + (1));
      junk_4 = 882;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
