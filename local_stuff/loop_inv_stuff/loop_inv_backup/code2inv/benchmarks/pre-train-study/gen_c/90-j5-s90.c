int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 7;
  int junk_3 = 5;
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
      junk_0 = junk_4 + (junk_3);
      x = y;
      junk_2 = 962 + (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 42;
      x = y;
      junk_0 = junk_0;
      y = ((y) + (1));
      junk_3 = 949 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
