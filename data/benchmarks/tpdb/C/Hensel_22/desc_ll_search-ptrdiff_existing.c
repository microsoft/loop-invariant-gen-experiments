#include <stdlib.h>

#ifndef __PTRDIFF_TYPE__
#define __PTRDIFF_TYPE__ long int
#endif
typedef __PTRDIFF_TYPE__ ptrdiff_t;

extern int __VERIFIER_nondet_int();

struct list {
  int value;
  struct list* next;
};

struct list* init_list(int n) {
  struct list* curr = NULL;
  struct list* tail = curr;

  for (int j = 0; j < n; j++) {
    curr = malloc(sizeof(struct list));
    curr->value = j;
    curr->next = tail;
    tail = curr;
  }

  return curr;
}

void search(struct list* head, int m) {
  ptrdiff_t skip = (void*)&head->next - (void*)&head->value;
  void* ptr = (void*) head;
  while(*(int*)ptr != m) {
    ptr = *((struct list**)(ptr + skip));
  }
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) return 0;
  int m = __VERIFIER_nondet_int();
  if (m < 1 || m >= n) return 0;
  struct list* head = init_list(n);
  search(head,m);
  return 0;
}
