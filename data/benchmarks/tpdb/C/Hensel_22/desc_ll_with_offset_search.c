#include <stdlib.h>

extern int __VERIFIER_nondet_int();

struct list {
  int value;
  struct list* next;
};

struct list* init_list(int n, int start) {
  struct list* curr = NULL;
  struct list* tail = curr;

  for (int j = start; j < start+n; j++) {
    curr = malloc(sizeof(struct list));
    curr->value = j;
    curr->next = tail;
    tail = curr;
  }

  return curr;
}

void search(struct list* head, int m) {
  struct list* curr = head;
  while(curr->value != m) {
    curr = curr->next;
  }
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) return 0;
  int m = __VERIFIER_nondet_int();
  if (m < 1 || m >= n) return 0;
  int start = __VERIFIER_nondet_int();
  struct list* head = init_list(n,start);
  search(head,start+m);
  return 0;
}
