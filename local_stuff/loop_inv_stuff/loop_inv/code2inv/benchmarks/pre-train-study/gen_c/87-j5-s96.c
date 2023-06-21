int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 2;
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
      junk_2 = junk_2 - (770);
      x = y;
      junk_0 = junk_2 + (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 757;
      x = y;
      junk_3 = junk_2;
      y = ((y) + (1));
      junk_1 = 434;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
