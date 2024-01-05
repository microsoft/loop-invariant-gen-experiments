#include <stdlib.h>

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
    curr->value = __VERIFIER_nondet_int();
    curr->next = tail;
    tail = curr;
  }

  return curr;
}

int main() {
  int n = __VERIFIER_nondet_int();
  struct list* head = init_list(n);
  return 0;
}
