int main()
{
  int i;
  int sn;
  int junk_0 = 1;
  int junk_1 = 0;
  int junk_2 = 3;
  //skip 
  sn = 0;
  
  i = 1;
  
  while(((i) <= (8)))
  {
    //tb 
    i = ((i) + (1));
    junk_2 = junk_1;
    sn = ((sn) + (1));
    junk_1 = junk_0;
  }
    //fb 
  if(((sn) != (0))) {
    //tb 
    assert ((sn) == (8));
  }
  else{
    //fb 
  }
  //skip 
  //skip 


}
