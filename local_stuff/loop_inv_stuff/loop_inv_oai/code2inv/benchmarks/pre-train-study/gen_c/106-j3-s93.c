int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 7;
  int junk_1 = 0;
  int junk_2 = 7;
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
      junk_1 = junk_2 - (806);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = junk_2;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
