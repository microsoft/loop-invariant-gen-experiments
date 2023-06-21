int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 7;
  int junk_2 = 0;
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
      junk_2 = 32;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = 611;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
