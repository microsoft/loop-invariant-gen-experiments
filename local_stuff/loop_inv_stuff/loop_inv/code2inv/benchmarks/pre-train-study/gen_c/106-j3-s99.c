int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 6;
  int junk_1 = 2;
  int junk_2 = 3;
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
      junk_2 = 788 + (junk_1);
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 153 + (junk_2);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
