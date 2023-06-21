int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 8;
  int junk_1 = 1;
  int junk_2 = 7;
  int junk_3 = 3;
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
      junk_3 = 515 + (junk_3);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_4 = 887 - (junk_0);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
