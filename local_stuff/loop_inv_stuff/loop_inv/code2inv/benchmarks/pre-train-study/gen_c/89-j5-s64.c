int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 7;
  int junk_4 = 5;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 784;
      x = y;
      junk_1 = 151;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 322 - (junk_3);
      x = y;
      junk_3 = junk_1 + (97);
      y = ((y) + (1));
      junk_0 = 775;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
