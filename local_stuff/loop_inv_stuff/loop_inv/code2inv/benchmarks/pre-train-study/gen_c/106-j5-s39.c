int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 5;
  int junk_1 = 7;
  int junk_2 = 3;
  int junk_3 = 5;
  int junk_4 = 5;
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
      junk_4 = junk_2 - (junk_3);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = 137;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
