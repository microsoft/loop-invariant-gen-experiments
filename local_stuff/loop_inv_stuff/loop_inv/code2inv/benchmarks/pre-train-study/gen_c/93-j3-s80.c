int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 1;
  int junk_2 = 5;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = 928;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_2 = junk_1;
      y = ((y) + (2));
      junk_0 = junk_2;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_0 = junk_1 - (junk_2);
      y = ((y) + (1));
      junk_2 = junk_2 - (457);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
