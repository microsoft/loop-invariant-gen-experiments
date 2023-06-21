int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 4;
  int junk_1 = 5;
  int junk_2 = 8;
  int junk_3 = 9;
  int junk_4 = 8;
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
      junk_0 = junk_2;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = junk_0;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
