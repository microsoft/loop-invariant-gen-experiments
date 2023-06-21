int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 9;
  int junk_2 = 5;
  int junk_3 = 8;
  int junk_4 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 119 - (junk_4);
      x = y;
      junk_4 = junk_4 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_4 - (junk_2);
      x = y;
      junk_1 = 339;
      y = ((y) + (1));
      junk_0 = 258 - (339);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
