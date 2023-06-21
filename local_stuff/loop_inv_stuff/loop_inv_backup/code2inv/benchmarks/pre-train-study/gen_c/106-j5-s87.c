int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 7;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 1;
  int junk_4 = 9;
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
      junk_3 = 856;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = junk_0 - (414);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
