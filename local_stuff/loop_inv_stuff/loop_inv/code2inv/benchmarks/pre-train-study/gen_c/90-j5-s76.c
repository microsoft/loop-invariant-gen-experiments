int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 5;
  int junk_3 = 3;
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
      junk_3 = junk_1;
      x = y;
      junk_1 = junk_3 + (junk_3);
    }
    else{
      //fb 
      lock = 0;
      junk_0 = 704;
      x = y;
      junk_1 = junk_1 - (junk_4);
      y = ((y) + (1));
      junk_3 = junk_3 - (91);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
