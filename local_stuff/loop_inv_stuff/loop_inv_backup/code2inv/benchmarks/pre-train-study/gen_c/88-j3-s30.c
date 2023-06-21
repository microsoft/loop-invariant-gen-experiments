int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_2;
      x = y;
      junk_2 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 337 - (5);
      x = y;
      junk_2 = 440;
      y = ((y) + (1));
      junk_0 = 404 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
