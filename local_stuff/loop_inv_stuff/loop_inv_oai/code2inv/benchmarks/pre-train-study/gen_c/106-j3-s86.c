int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 6;
  int junk_1 = 5;
  int junk_2 = 4;
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
      junk_1 = 517 + (junk_0);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 823;
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
