int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 9;
  int junk_2 = 2;
  int junk_3 = 4;
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
      junk_2 = 757 - (junk_4);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_3 = 447;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
