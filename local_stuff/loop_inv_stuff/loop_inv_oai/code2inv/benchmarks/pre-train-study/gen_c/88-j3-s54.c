int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 9;
  int junk_2 = 3;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = junk_0 + (junk_2);
      x = y;
      junk_0 = 707 + (787);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0 + (junk_1);
      x = y;
      junk_2 = junk_2 - (junk_2);
      y = ((y) + (1));
      junk_1 = 290;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
