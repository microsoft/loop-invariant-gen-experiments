int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 3;
  int junk_2 = 1;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_2 + (389);
      x = y;
      junk_3 = 667;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 772;
      x = y;
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_1 = 773 - (562);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
