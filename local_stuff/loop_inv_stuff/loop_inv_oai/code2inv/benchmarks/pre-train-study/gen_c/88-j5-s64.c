int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 4;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 0;
  int junk_4 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_2 = 620 + (555);
      x = y;
      junk_2 = junk_4;
    }
    else{
      //fb 
      lock = 0;
      junk_2 = 207 + (junk_3);
      x = y;
      junk_3 = 22 + (777);
      y = ((y) + (1));
      junk_3 = junk_3 + (44);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
