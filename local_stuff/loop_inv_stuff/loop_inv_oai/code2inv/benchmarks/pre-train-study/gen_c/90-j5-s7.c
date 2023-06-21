int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 1;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 4;
  int junk_4 = 9;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_3 = junk_0 + (junk_3);
      x = y;
      junk_3 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 63;
      x = y;
      junk_0 = junk_4;
      y = ((y) + (1));
      junk_1 = 569;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
