int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 0;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = junk_1 + (junk_0);
      x = y;
      junk_1 = junk_2;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 959 - (942);
      x = y;
      junk_2 = 763;
      y = ((y) + (1));
      junk_1 = 931;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
