int main()
{
  int a;
  int c;
  int j;
  int k;
  int m;
  int junk_0 = 9;
  int junk_1 = 8;
  int junk_2 = 8;
  int junk_3 = 4;
  int junk_4 = 4;
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
      junk_2 = junk_3;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = junk_1;
  }
    //fb 
  assert ((a) <= (m));
  //skip 


}
