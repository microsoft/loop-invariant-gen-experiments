int main()
{
  int lock;
  int tmp;
  int x;
  int y;
  int junk_0 = 0;
  //skip 
  x = y;
  
  lock = 1;
  
  while(((x) != (y)))
  {
    //tb 
    if(unknown()) {
      //tb 
      lock = 1;
      junk_0 = 152 - (44);
      x = y;
      junk_0 = junk_0;
    }
    else{
      //fb 
      lock = 0;
      junk_0 = junk_0;
      x = y;
      junk_0 = 171 - (386);
      y = ((y) + (1));
      junk_0 = 326 - (junk_0);
    }
  }
    //fb 
  assert ((lock) == (1));
  //skip 


}
