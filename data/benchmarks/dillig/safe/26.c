
void alloc_fixed_size(int** a, int size, int n, int k)
{
   int i;
   for( i=0; i<n; i++){
       a[i] = malloc(sizeof(int)*size);
   }
   if(n>=0 && k>=0 && k<n) {
       buffer_safe(a[k], size-1);
   }  
}

