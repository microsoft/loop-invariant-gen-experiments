int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 1;
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
    junk_0 = junk_0 - (662);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = junk_3;
      y = ((y) + (2));
      junk_4 = junk_3;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = junk_3;
      y = ((y) + (1));
      junk_3 = 636 - (770);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
