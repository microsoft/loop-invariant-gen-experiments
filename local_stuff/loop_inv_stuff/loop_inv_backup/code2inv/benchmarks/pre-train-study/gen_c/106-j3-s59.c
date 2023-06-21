int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 4;
  int junk_1 = 1;
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
      junk_1 = 722;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_2 = 740 - (529);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
