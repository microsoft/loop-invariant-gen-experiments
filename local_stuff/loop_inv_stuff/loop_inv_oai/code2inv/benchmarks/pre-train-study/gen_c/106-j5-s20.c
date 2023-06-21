int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 4;
  int junk_1 = 8;
  int junk_2 = 0;
  int junk_3 = 0;
  int junk_4 = 1;
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
      junk_4 = 158 - (junk_0);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = 117;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
