int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 4;
  int junk_4 = 6;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_4 = junk_1;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = junk_1 - (399);
      y = ((y) + (2));
      junk_4 = 21;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = junk_0 - (762);
      y = ((y) + (1));
      junk_3 = 512;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
