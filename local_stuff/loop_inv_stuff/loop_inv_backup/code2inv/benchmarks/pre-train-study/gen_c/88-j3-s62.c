int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 7;
  int junk_2 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 509 + (526);
      x = y;
      junk_2 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 776 + (junk_2);
      x = y;
      junk_2 = junk_1;
      y = ((y) + (1));
      junk_2 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
