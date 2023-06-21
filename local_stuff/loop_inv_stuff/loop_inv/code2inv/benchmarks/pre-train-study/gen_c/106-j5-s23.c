int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 0;
  int junk_2 = 4;
  int junk_3 = 9;
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
      junk_3 = junk_2 + (280);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 155 + (827);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
