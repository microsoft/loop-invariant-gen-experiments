int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  int junk_1 = 7;
  int junk_2 = 8;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 70;
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 635;
      x = y;
      junk_1 = 968 + (junk_1);
      y = ((y) + (1));
      junk_0 = 145 + (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
