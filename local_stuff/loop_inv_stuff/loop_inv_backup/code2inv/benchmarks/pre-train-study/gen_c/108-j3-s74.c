int main()
{
  int a;
  int c;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 4;
  int junk_2 = 4;
  //skip 
  assume ((a) <= (m));
  j = 0;
  
  k = 0;
  
  while(((k) < (c)))
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
    junk_0 = 120 - (junk_0);
  }
    //fb 
  assert ((a) <= (m));
  //skip 


}
