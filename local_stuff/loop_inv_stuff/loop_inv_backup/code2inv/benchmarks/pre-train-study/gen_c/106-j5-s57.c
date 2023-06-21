int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 9;
  int junk_3 = 2;
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
      junk_0 = junk_1;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 889 - (junk_2);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
