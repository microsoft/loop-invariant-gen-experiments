int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 4;
  int junk_2 = 3;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1;
      x = y;
      junk_1 = 803;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2;
      x = y;
      junk_2 = 467 - (388);
      y = ((y) + (1));
      junk_2 = 374;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
