int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 3;
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
      junk_0 = 129;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = 495 + (junk_0);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
