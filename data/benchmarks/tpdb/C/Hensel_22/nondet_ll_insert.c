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

void insert(struct list** head_ptr, int m) {
  struct list* head = *head_ptr;
  struct list* new = malloc(sizeof(struct list));
  new->value = m;

  if (head == NULL || head->value >= m) {
    new->next = head;
    *head_ptr = new;
    return;
  }

  struct list* curr = head;
  while(curr->next != NULL && curr->next->value < m) {
    curr = curr->next;
  }

  new->next = curr->next;
  curr->next = new;

  *head_ptr = head;
}

int main() {
  int n = __VERIFIER_nondet_int();
  if (n < 1) return 0;
  int m = __VERIFIER_nondet_int();
  struct list* head = init_list(n);
  insert(&head,m);
  return 0;
}
