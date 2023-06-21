int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 7;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_1 = junk_2 + (junk_2);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_2 + (893);
      x = y;
      junk_1 = 650;
      y = ((y) + (1));
      junk_1 = junk_1 + (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
