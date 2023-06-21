int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 1;
  int junk_2 = 2;
  int junk_3 = 5;
  int junk_4 = 8;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_1 + (896);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = junk_0 - (220);
      y = ((y) + (2));
      junk_2 = junk_2;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_4 = 348 + (junk_4);
      y = ((y) + (1));
      junk_4 = 566 + (junk_4);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
