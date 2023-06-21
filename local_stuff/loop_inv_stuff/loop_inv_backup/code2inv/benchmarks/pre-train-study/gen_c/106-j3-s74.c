int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 4;
  int junk_1 = 2;
  int junk_2 = 6;
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
      junk_0 = junk_0;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = 651;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
