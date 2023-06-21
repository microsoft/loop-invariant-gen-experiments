int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 3;
  int junk_1 = 5;
  int junk_2 = 5;
  int junk_3 = 0;
  int junk_4 = 6;
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
      junk_3 = junk_2 - (18);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = junk_3 - (72);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
