int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_0 + (375);
      x = y;
      junk_0 = 345 + (603);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_0 = 335;
      y = ((y) + (1));
      junk_0 = 995;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
