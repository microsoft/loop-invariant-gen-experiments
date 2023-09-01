#include "seahorn/seahorn.h"

extern int unknown ();

/* C implementation QuickSort */
//#include<stdio.h>
 
// A utility function to swap two elements
void swap(int* a, int* b)
{
    int t = *a;
    *a = *b;
    *b = t;
}
 
/* This function takes last element as pivot, places
   the pivot element at its correct position in sorted
    array, and places all smaller (smaller than pivot)
   to left of pivot and all greater elements to right
   of pivot */
int partition (int low, int high)
{
    int pivot = unknown(); //arr[high];    // pivot
    int i = (low - 1);  // Index of smaller element
 
    for (int j = low; j <= high-1; j++)
    {
        // If current element is smaller than or
        // equal to pivot
        if (unknown())
        //if (arr[j] <= pivot)
        {
            i++;    // increment index of smaller element
            sassert (low <= i && i <= high);
            sassert (low <= j && j <= high);
            //swap(&arr[i], &arr[j]);
        }
    }
    //swap(&arr[i + 1], &arr[high]);
    return (i + 1);
}
 
/* The main function that implements QuickSort
 arr[] --> Array to be sorted,
  low  --> Starting index,
  high  --> Ending index */
void quickSort(int low, int high)
{
    if (low < high)
    {
        /* pi is partitioning index, arr[p] is now
           at right place */
        int pi = partition(low, high);
        
        sassert (low <= pi && pi <= high);
 
        // Separately sort elements before
        // partition and after partition
        quickSort(low, pi - 1);
        quickSort(pi + 1, high);
    }
}
 
// Driver program to test above functions
int main()
{
    int n = unknown ();
    quickSort(0, n-1);
    return 0;
}