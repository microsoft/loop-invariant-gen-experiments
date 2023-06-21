int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 383;
      x = y;
      junk_2 = 654 + (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 396 + (junk_2);
      x = y;
      junk_1 = junk_1;
      y = ((y) + (1));
      junk_1 = 583 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
