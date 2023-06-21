int main()
{
  int a;
  int c;
  int j;
  int k;
  int m;
  int junk_0 = 1;
  int junk_1 = 5;
  int junk_2 = 6;
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
      junk_0 = 204;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = junk_2 - (junk_0);
  }
    //fb 
  assert ((a) <= (m));
  //skip 


}
