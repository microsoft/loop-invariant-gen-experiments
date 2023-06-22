int unknown1(){
    int x; return x;
}

int unknown2();
int unknown3();
int unknown4();

void main(int argc, char* argv[]) {

  int n;
  int i, k, j;


  n = unknown1();
  if(n < 1)
    return;
  if(k < n)
    return;
  j = 0;
  while( j <= n-1 ) {
    j++;
    k--;
  } 
  if(j < n)
    return;
  if(k <= -1)
  {goto ERROR;ERROR:;}
}
