#include "myassert.h"


void main () {
int i, j;
int from;
int to;
int k;

if (!(k >= 0)) return;
if (!(k <= 100)) return;

if (!(from >= 0)) return;
if (!(from <= k)) return;

i = from;
j = 0;

while (i < k) {
i++;
j++;
}

__VERIFIER_assert(j <= 100);

}

