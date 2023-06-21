int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 3;
  int junk_1 = 7;
  int junk_2 = 2;
  //skip 
  y = ((x) + (1));
  
  lock = 0;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_1 = 273;
      x = y;
      junk_2 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_1 = 729 + (junk_0);
      x = y;
      junk_2 = 898 + (258);
      y = ((y) + (1));
      junk_2 = 406;
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
