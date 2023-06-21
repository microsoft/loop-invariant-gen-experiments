int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 4;
  int junk_1 = 4;
  int junk_2 = 3;
  int junk_3 = 6;
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
      junk_3 = junk_2;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 65 + (481);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
