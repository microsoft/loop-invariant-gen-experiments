#include <stdlib.h>

extern int __VERIFIER_nondet_int();

struct list {
  int value;
  struct list* next;
};

struct list* init_list(int n) {
  if (n == 0) return NULL;
  struct list* curr = malloc(sizeof(struct list));
  curr->value = __VERIFIER_nondet_int();
  curr->next = init_list(n-1);
  return curr;
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) return 0;
  struct list* head = init_list(n);
  return 0;
}
