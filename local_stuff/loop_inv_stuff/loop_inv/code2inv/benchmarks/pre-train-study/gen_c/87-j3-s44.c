int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 794;
      x = y;
      junk_2 = 398;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 170;
      x = y;
      junk_0 = junk_2;
      y = ((y) + (1));
      junk_2 = junk_2 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
