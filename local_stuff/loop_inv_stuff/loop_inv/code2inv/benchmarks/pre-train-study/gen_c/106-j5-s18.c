int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 6;
  int junk_2 = 7;
  int junk_3 = 4;
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
      junk_1 = 589 - (junk_0);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = junk_0 - (junk_3);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
