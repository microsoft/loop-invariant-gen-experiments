int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 5;
  int junk_2 = 0;
  int junk_3 = 1;
  int junk_4 = 9;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 385;
      x = y;
      junk_3 = 385;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 794;
      x = y;
      junk_2 = junk_2 + (junk_3);
      y = ((y) + (1));
      junk_3 = 903 - (595);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
