int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 4;
  int junk_2 = 6;
  int junk_3 = 5;
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
      junk_1 = junk_2 + (555);
      x = y;
      junk_0 = junk_1 - (13);
    }
    else{
      //fb 
      lock = 0;
      junk_4 = junk_0 + (junk_0);
      x = y;
      junk_4 = junk_3;
      y = ((y) + (1));
      junk_0 = 398 + (958);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
