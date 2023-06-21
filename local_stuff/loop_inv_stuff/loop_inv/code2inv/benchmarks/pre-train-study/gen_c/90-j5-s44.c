int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 5;
  int junk_4 = 7;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_4 = 306 - (junk_2);
      x = y;
      junk_2 = 244;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 909;
      x = y;
      junk_4 = 317;
      y = ((y) + (1));
      junk_4 = junk_1;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
