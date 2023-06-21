int main()
{
  int a;
  int c;
  int j;
  int k;
  int m;
  int junk_0 = 5;
  int junk_1 = 0;
  int junk_2 = 2;
  int junk_3 = 4;
  int junk_4 = 0;
  //skip 
  assume ((a) <= (m));
  j = 0;
  
  k = 0;
  
  while(((k) < (c)))
  {
    //tb 
    if(((m) < (a))) {
      //tb 
      m = a;
      junk_0 = junk_2;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 143 + (junk_4);
  }
    //fb 
  assert ((a) <= (m));
  //skip 


}
