int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 2;
  int junk_2 = 6;
  int junk_3 = 6;
  int junk_4 = 8;
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
      junk_2 = 446 + (junk_2);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = junk_0 - (253);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
