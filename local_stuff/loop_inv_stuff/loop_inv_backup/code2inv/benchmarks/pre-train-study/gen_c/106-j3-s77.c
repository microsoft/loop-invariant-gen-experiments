int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 8;
  int junk_1 = 8;
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
      junk_0 = 460 + (junk_0);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 409;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
