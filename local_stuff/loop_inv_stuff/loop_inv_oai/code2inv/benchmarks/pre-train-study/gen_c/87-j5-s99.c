int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 7;
  int junk_2 = 7;
  int junk_3 = 9;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 930 + (junk_2);
      x = y;
      junk_2 = 339;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = junk_3 - (335);
      x = y;
      junk_4 = junk_4 - (junk_1);
      y = ((y) + (1));
      junk_4 = junk_3;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
