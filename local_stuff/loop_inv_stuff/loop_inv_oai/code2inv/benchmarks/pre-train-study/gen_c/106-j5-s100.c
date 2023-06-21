int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 1;
  int junk_2 = 1;
  int junk_3 = 2;
  int junk_4 = 0;
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
      junk_0 = junk_3 - (724);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 57;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
