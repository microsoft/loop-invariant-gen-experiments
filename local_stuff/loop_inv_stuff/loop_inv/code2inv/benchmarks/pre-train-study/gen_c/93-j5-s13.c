int main()
{
  int i;
  int n;
  int tmp;
  int x;
  int y;
  int junk_0 = 6;
  int junk_1 = 6;
  int junk_2 = 4;
  int junk_3 = 8;
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
    junk_0 = 442 + (512);
    if(unknown()) {
      //tb 
      x = ((x) + (1));
      junk_1 = 692;
      y = ((y) + (2));
      junk_4 = 808;
    }
    else{
      //fb 
      x = ((x) + (2));
      junk_3 = 865;
      y = ((y) + (1));
      junk_4 = 181 + (junk_1);
    }
  }
    //fb 
  assert ((((3) * (n))) == (((x) + (y))));
  //skip 


}
