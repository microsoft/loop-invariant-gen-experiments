int unknown1(){
    int x; return x;
}

int unknown2(){
    int x; return x;
}



int main()
{
  int flag = unknown1();
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  int x,y;
  while(unknown1()){
    a++;
    b++;
    s+=a;
    t+=b;
    if(flag){
      t+=a;
    }
    t = t;
  } 
  //2s >= t
  x = 1;
  if(flag){
    x = t-2*s+2;
  }
  //x <= 2
  y = 0;
  while(y<=x){
    if(unknown2()) 
       y++;
    else 
       y+=2;
    y = y;
  }
  if(y >= 5)
  {goto ERROR; ERROR:;}
}

