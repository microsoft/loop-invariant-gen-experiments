int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 2;
  int junk_1 = 2;
  int junk_2 = 2;
  int junk_3 = 2;
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
      junk_4 = 317;
      x = y;
      junk_0 = 482;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 627;
      x = y;
      junk_4 = junk_0 - (933);
      y = ((y) + (1));
      junk_2 = 204 - (junk_2);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
