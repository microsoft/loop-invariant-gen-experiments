int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 1;
  int junk_1 = 8;
  int junk_2 = 3;
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
      junk_1 = junk_0;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = junk_1;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
