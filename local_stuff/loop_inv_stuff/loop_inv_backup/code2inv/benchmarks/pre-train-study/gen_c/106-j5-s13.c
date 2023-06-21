int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 8;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 2;
  int junk_4 = 4;
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
      junk_0 = 971 - (junk_2);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = junk_1;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
