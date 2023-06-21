int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 8;
  int junk_1 = 5;
  int junk_2 = 3;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_0 = junk_0 + (junk_1);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_1 = 103;
      y = ((y) + (2));
      junk_1 = 921;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = 704;
      y = ((y) + (1));
      junk_1 = 584;
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
