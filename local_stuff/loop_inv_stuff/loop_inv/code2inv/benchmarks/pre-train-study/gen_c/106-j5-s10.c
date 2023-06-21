int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 5;
  int junk_1 = 4;
  int junk_2 = 2;
  int junk_3 = 5;
  int junk_4 = 9;
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
      junk_0 = 116 - (junk_1);
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
