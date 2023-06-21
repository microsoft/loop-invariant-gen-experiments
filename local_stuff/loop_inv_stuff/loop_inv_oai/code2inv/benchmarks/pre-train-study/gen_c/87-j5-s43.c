int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 4;
  int junk_2 = 4;
  int junk_3 = 8;
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
      junk_0 = 227 + (191);
      x = y;
      junk_3 = junk_2 - (732);
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 423;
      x = y;
      junk_0 = 426 - (junk_2);
      y = ((y) + (1));
      junk_3 = junk_3;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
