int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 9;
  int junk_3 = 5;
  int junk_4 = 3;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 888;
      x = y;
      junk_1 = 873 + (junk_4);
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 404;
      x = y;
      junk_2 = 477 + (junk_4);
      y = ((y) + (1));
      junk_2 = 22 + (715);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
