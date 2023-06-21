int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_2;
      x = y;
      junk_2 = 926 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (junk_2);
      x = y;
      junk_2 = 236;
      y = ((y) + (1));
      junk_1 = 555 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
