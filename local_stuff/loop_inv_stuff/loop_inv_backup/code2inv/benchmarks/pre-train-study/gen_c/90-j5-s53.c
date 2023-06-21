int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 0;
  int junk_2 = 5;
  int junk_3 = 3;
  int junk_4 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 88 - (junk_2);
      x = y;
      junk_1 = 755;
    }
    else{
      //fb 
      lock = 0;
      junk_4 = 449;
      x = y;
      junk_2 = junk_3;
      y = ((y) + (1));
      junk_1 = 704;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
