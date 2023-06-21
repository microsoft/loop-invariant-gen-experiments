int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 5;
  int junk_1 = 3;
  int junk_2 = 9;
  int junk_3 = 1;
  int junk_4 = 2;
  //skip 
  assume ((n) >= (0));
  i = 0;
  
  x = 0;
  
  y = 0;
  
  while(((i) < (n)))
  {
    //tb 
    i = ((i) + (1));
    junk_1 = 999;
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_0 = junk_1 - (674);
      y = ((y) + (2));
      junk_1 = junk_3 - (junk_1);
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_2 = 614;
      y = ((y) + (1));
      junk_0 = junk_2 - (junk_2);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
