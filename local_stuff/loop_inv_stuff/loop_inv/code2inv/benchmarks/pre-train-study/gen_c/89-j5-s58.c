int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 5;
  int junk_3 = 4;
  int junk_4 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = 258 + (445);
      x = y;
      junk_3 = 57 - (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_1;
      x = y;
      junk_2 = 18 + (442);
      y = ((y) + (1));
      junk_2 = 582 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
