int main()
{
  int a;
  int j;
  int k;
  int m;
  int junk_0 = 3;
  int junk_1 = 3;
  int junk_2 = 8;
  int junk_3 = 8;
  int junk_4 = 0;
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
      junk_4 = 999;
    }
    else{
      //fb 
    }
    //phi 
    k = ((k) + (1));
    junk_0 = 726 - (340);
  }
    //fb 
  assert ((a) >= (m));
  //skip 


}
