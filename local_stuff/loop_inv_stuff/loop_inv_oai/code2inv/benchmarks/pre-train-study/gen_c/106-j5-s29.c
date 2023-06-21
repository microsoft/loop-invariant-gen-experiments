int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 1;
  int junk_1 = 6;
  int junk_2 = 6;
  int junk_3 = 3;
  int junk_4 = 7;
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
      junk_4 = 985 - (951);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = junk_3 + (junk_0);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
