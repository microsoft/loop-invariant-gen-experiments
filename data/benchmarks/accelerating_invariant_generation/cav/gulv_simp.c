int nondet(){
  int x;
  return x;
}

int main(){
int x = 0, y = 0;
while (nondet()) {
   if (nondet())
     {x = x+1; y = y+100;}
   else if (nondet()){
     if (x >= 4)
       {x = x+1; y = y+1;}
   }
 /*else if (y > 10*w && z >= 100*x)
     {y = -y;}
   w = w+1; z = z+10;*/
   x = x; /* work around VC gen bug */
}
if (x >= 4 && y <= 2)
  goto ERROR;

return;
ERROR:;
}
