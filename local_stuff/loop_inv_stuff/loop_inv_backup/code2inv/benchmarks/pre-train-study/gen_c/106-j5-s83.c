int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 6;
  int junk_1 = 5;
  int junk_2 = 1;
  int junk_3 = 0;
  int junk_4 = 1;
  //skip 
  assume ((a) <= (m));
  assume ((j) < (1));
  k = 0;
  
  while(((k) < (1)))
  {
    //tb 
    if(((m) < (a))) {
      //tb 
      m = a;
      junk_2 = junk_1 + (798);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = 672 - (junk_3);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
