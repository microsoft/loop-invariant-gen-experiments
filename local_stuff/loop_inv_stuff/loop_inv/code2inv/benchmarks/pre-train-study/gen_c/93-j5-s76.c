int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 6;
  int junk_2 = 6;
  int junk_3 = 8;
  int junk_4 = 0;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_4;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_3 = 164 + (567);
      y = ((y) + (2));
      junk_3 = 204;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_1 = junk_4;
      y = ((y) + (1));
      junk_1 = junk_4;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
