int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 1;
  int junk_1 = 3;
  int junk_2 = 5;
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
      junk_2 = 208 - (junk_0);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = junk_2 + (junk_2);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
