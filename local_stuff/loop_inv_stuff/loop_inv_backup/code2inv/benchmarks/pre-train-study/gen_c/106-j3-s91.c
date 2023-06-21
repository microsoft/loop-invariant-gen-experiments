int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 2;
  int junk_1 = 4;
  int junk_2 = 8;
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
      junk_0 = 95;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = junk_1 + (452);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
