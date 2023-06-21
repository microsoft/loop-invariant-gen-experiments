int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 1;
  int junk_2 = 5;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 844 + (152);
      x = y;
      junk_0 = 217;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_0;
      x = y;
      junk_0 = junk_1 + (43);
      y = ((y) + (1));
      junk_1 = junk_0 + (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
