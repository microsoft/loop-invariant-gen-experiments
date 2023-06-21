int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 5;
  int junk_2 = 6;
  int junk_3 = 3;
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
      junk_0 = 83 + (junk_1);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = junk_4 - (304);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
