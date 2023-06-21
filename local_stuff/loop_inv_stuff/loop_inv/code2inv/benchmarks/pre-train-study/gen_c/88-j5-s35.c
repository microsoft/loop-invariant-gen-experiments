int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 3;
  int junk_3 = 3;
  int junk_4 = 6;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = junk_1;
      x = y;
      junk_3 = junk_4 + (594);
    }
    else{
      //fb 
      lock = 0;
      junk_2 = junk_1 - (junk_4);
      x = y;
      junk_1 = 897;
      y = ((y) + (1));
      junk_0 = junk_2;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
