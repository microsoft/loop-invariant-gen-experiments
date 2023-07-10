/*
Commit Number: ec79a06d084e7f7508fcfad583258163d8066e7b
URL: https://github.com/freeciv/freeciv/commit/ec79a06d084e7f7508fcfad583258163d8066e7b
Project Name: freeciv
License: GPL-2.0
termination: TRUE
*/
#define A_NONE 0
#define NULL 0
#define A_FIRST 1
#define MAX_NUM_ADVANCES 10
#define A_LAST (MAX_NUM_ADVANCES + 1) /* Used in the network protocol. */
#define A_FUTURE (A_LAST + 1)
#define A_ARRAY_SIZE (A_FUTURE + 1)
#define A_UNSET (A_LAST + 2)
#define A_UNKNOWN (A_LAST + 3)

#define A_NEVER (NULL)
typedef int Tech_type_id;
enum tech_req {
  AR_ONE = 0,
  AR_TWO = 1,
  AR_ROOT = 2,
  AR_SIZE
};
struct advance{
    Tech_type_id item_number;
    struct advance *require[AR_SIZE];
};
struct advance advances[10];


//6
Tech_type_id advance_number(const struct advance *padvance)
{
  return padvance->item_number;
}
//5 ->6
Tech_type_id advance_required(const Tech_type_id tech, enum tech_req require)
{

  if (A_NEVER == advances[tech].require[require]) {
    /* out of range */
    return A_LAST;
  }
  return advance_number(advances[tech].require[require]);
}

//4
struct advance *valid_advance(struct advance *padvance)
{
  if (NULL == padvance) {
    return NULL;
  }
  return padvance;
}

// 3
struct advance *advance_by_number(const Tech_type_id atype)
{
  if (atype != A_FUTURE && atype < 0 ) {
    /* This isn't an error; some callers depend on it. */
    return NULL;
  }

  return &advances[atype];
}
// 2->3, 4
struct advance *valid_advance_by_number(const Tech_type_id id)
{
  return valid_advance(advance_by_number(id));
}
// 1->2  ->5
int player_invention_reachable(const Tech_type_id tech, int allow_prereqs)
{
    Tech_type_id root;
    if (!valid_advance_by_number(tech)) {
        return 0;
    }
    root = advance_required(tech, AR_ROOT);
    if (A_NONE != root) {
        if(root == tech)
            return 0;
        else if (allow_prereqs) {
            return player_invention_reachable(root, 1);
        }
        return 0;
    }
    return 1;
}

int main()
{
    for( int i = 0 ; i <10 ; i++)
    {
        advances[i].item_number =  4;
        for( int j = 0 ; j < 3 ; j++ )
        {
            struct advance req;
            req.item_number =  1;
            advances[i].require[j] = &req;
        }
    }
    int tech = __VERIFIER_nondet_int();
    tech = tech % 8;
    int allow_prereqs = __VERIFIER_nondet_int();
    int ok = player_invention_reachable(tech,allow_prereqs);
    return 0;
}
