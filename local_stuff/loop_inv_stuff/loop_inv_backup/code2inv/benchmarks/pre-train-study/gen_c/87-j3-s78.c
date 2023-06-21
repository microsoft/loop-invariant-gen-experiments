int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 0;
  int junk_2 = 4;
  //skip 
  x = y;
  
  lock = 1;
  
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
      junk_0 = 110 + (junk_2);
      x = y;
      junk_2 = junk_1 - (163);
      y = ((y) + (1));
      junk_1 = 34 + (19);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
