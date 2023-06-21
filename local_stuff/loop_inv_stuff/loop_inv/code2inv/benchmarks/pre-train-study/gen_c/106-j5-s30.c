int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 3;
  int junk_2 = 4;
  int junk_3 = 3;
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
      junk_2 = junk_2;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = 428;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
