int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 6;
  int junk_1 = 2;
  int junk_2 = 8;
  int junk_3 = 8;
  int junk_4 = 2;
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
      junk_0 = 765;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = 880 + (junk_2);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
