int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 7;
  int junk_1 = 4;
  int junk_2 = 5;
  int junk_3 = 1;
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
      junk_3 = junk_2 + (271);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = 196;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
