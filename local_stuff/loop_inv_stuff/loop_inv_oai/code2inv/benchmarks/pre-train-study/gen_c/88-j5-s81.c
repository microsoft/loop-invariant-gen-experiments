int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 9;
  int junk_2 = 3;
  int junk_3 = 8;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 466;
      x = y;
      junk_2 = 58;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_3;
      x = y;
      junk_0 = junk_2 + (950);
      y = ((y) + (1));
      junk_1 = junk_2 - (631);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
