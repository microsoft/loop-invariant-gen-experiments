int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 9;
  int junk_1 = 3;
  int junk_2 = 9;
  int junk_3 = 0;
  int junk_4 = 3;
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
      junk_0 = junk_3;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = 54;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
