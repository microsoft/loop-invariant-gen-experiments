int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 9;
  int junk_1 = 0;
  int junk_2 = 7;
  int junk_3 = 2;
  int junk_4 = 3;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_3 = junk_1;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_4 = 930 - (junk_0);
      y = ((y) + (2));
      junk_0 = junk_0 - (36);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = 615 + (junk_2);
      y = ((y) + (1));
      junk_1 = 632 + (985);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
