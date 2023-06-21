int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 8;
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
      junk_0 = 910;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = 446 + (junk_0);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
