 #include "seahorn/seahorn.h"

extern int unknown();

// This is an iterative version of merge sort.
// It merges pairs of two consecutive lists one after another.
// After scanning the whole array to do the above job,
// it goes to the next stage. Variable k controls the size
// of lists to be merged. k doubles each time the main loop
// is executed.
//#include <stdio.h>
//#include <math.h>

//int a[100000],b[100000];

int min(int x, int y) { return (x<y)? x :y; }

void merge (int l, int m, int r)
//void merge(int arr[], int l, int m, int r)
{
    int i, j, k;
    int n1 = m - l + 1;
    int n2 =  r - m;
 
    /* create temp arrays */
    //int L[n1], R[n2];
 
    /* Copy data to temp arrays L[] and R[] */
    for (i = 0; i < n1; i++)
        //L[i] = arr[l + i];
    for (j = 0; j < n2; j++)
        //R[j] = arr[m + 1+ j];
 
    /* Merge the temp arrays back into arr[l..r]*/
    i = 0;
    j = 0;
    k = l;
    while (i < n1 && j < n2)
    {
        if (unknown())
	//if (L[i] <= R[j])
        {
            //arr[k] = L[i];
            i++;
        }
        else
        {
            //arr[k] = R[j];
            j++;
        }
        k++;
    }

    sassert (k <= r);
 
    /* Copy the remaining elements of L[], if there are any */
    while (i < n1)
    {
	sassert (k <= r);
        //arr[k] = L[i];
        i++;
        k++;
    }
 
    /* Copy the remaining elements of R[], if there are any */
    while (j < n2)
    {
	sassert (k <= r);
        //arr[k] = R[j];
        j++;
        k++;
    }
}

void mergeSort (int n)
//void mergeSort(int arr[], int n)
{
   int curr_size;  // For current size of subarrays to be merged
                   // curr_size varies from 1 to n/2
   int left_start; // For picking starting index of left subarray
                   // to be merged
 
   // Merge subarrays in bottom up manner.  First merge subarrays of
   // size 1 to create sorted subarrays of size 2, then merge subarrays
   // of size 2 to create sorted subarrays of size 4, and so on.
   for (curr_size=1; curr_size<=n-1; curr_size = 2*curr_size)
   {
       // Pick starting point of different subarrays of current size
       for (left_start=0; left_start<n-1; left_start += 2*curr_size)
       {
           // Find ending point of left subarray. mid+1 is starting 
           // point of right
           int mid = left_start + curr_size - 1;
 
           int right_end = min(left_start + 2*curr_size - 1, n-1);
 
           // Merge Subarrays arr[left_start...mid] & arr[mid+1...right_end]
           merge(left_start, mid, right_end);
       }
   }
}


void main()
{ 
  int n = unknown ();

  mergeSort (n);
}

/*
main()
{ printf("input size \n");
  scanf("%d",&n); 
  for (i=1;i<=n;i++) a[i]=random()%1000;
  t=clock();
  sort1();
  for (i=1;i<=10;i++) printf("%d ",a[i]);
  printf("\n");
  printf("time= %d millisec\n",(clock()-t)/1000);
}
*/
