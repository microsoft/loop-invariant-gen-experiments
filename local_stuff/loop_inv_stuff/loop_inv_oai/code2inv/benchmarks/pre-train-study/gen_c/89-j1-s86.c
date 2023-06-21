int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 72;
      x = y;
      junk_0 = junk_0 + (555);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 - (13);
      x = y;
      junk_0 = junk_0 + (junk_0);
      y = ((y) + (1));
      junk_0 = junk_0;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
