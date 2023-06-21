int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 0;
  int junk_4 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 549;
      x = y;
      junk_3 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 421 + (junk_3);
      x = y;
      junk_4 = junk_3;
      y = ((y) + (1));
      junk_3 = 901 + (junk_4);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
