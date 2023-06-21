int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 9;
  int junk_1 = 7;
  int junk_2 = 1;
  int junk_3 = 8;
  int junk_4 = 5;
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
      junk_3 = junk_1 - (437);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = junk_3;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
