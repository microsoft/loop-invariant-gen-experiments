int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 7;
  int junk_2 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 776 + (585);
      x = y;
      junk_1 = 347 - (579);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1;
      x = y;
      junk_0 = junk_1;
      y = ((y) + (1));
      junk_1 = 514;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
