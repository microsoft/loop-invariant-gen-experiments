int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 6;
  int junk_3 = 9;
  int junk_4 = 0;
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
      junk_1 = 166 - (767);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 755;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
