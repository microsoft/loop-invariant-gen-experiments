int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 4;
  int junk_2 = 5;
  int junk_3 = 6;
  int junk_4 = 2;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 775;
      x = y;
      junk_4 = junk_3;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 835;
      x = y;
      junk_4 = 76;
      y = ((y) + (1));
      junk_0 = 168;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
