int main()
{
  int a;
  int c;
  int j;
  int k;
  int m;
  int junk_0 = 0;
  int junk_1 = 7;
  int junk_2 = 2;
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
      junk_2 = junk_0 + (junk_2);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_1 = junk_1;
  }
    //fb 
  assert ((a) <= (m));
  //skip 


}
