int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 8;
  int junk_2 = 2;
  int junk_3 = 3;
  int junk_4 = 8;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = junk_1;
      x = y;
      junk_3 = 686;
    }
    else{
      //fb 
      lock = 0;
      junk_3 = 949;
      x = y;
      junk_0 = 896;
      y = ((y) + (1));
      junk_0 = 222 + (472);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
