int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 1;
  int junk_2 = 1;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1 + (junk_1);
      x = y;
      junk_1 = junk_2 + (junk_1);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 682;
      x = y;
      junk_1 = junk_0;
      y = ((y) + (1));
      junk_0 = 185 + (572);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
