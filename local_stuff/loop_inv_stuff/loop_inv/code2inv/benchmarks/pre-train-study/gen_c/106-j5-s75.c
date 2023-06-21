int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 9;
  int junk_1 = 1;
  int junk_2 = 9;
  int junk_3 = 7;
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
      junk_1 = 188;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 846;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
