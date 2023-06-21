int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 3;
  int junk_2 = 1;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 851;
      x = y;
      junk_1 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 214 + (135);
      x = y;
      junk_2 = 422 - (junk_0);
      y = ((y) + (1));
      junk_1 = junk_1 - (junk_1);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
