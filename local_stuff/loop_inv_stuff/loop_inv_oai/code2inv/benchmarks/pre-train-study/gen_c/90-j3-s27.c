int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 4;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_2 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 490 + (638);
      x = y;
      junk_0 = 786;
      y = ((y) + (1));
      junk_0 = junk_0 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
