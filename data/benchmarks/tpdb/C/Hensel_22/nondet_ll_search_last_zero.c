#include <stdlib.h>

extern int __VERIFIER_nondet_int();

struct list {
  int value;
  struct list* next;
};

struct list* init_list(int n) {
  struct list* tail = NULL;
  struct list* curr = malloc(sizeof(struct list));
  curr->value = 0;
  curr->next = tail;
  tail = curr;

  for (int j = 1; j < n; j++) {
    curr = malloc(sizeof(struct list));
    curr->value = __VERIFIER_nondet_int();
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
  struct list* head = init_list(n);
  search(head,0);
  return 0;
}
