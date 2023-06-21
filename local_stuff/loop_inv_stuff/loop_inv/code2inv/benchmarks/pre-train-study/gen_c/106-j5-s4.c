int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 9;
  int junk_2 = 3;
  int junk_3 = 5;
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
      junk_0 = junk_3;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = junk_2 + (junk_0);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
