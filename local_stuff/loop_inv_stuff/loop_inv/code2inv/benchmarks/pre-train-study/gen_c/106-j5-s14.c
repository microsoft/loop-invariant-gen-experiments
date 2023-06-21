int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 7;
  int junk_1 = 7;
  int junk_2 = 8;
  int junk_3 = 3;
  int junk_4 = 2;
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
      junk_2 = 295;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 514;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
