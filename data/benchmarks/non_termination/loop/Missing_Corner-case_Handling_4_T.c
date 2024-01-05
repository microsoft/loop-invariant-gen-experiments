/*
Commit Number: 6a603b5b55262c443bf780f3c112a586cb3d9901
URL: https://github.com/ArtifexSoftware/mupdf/commit/6a603b5b55262c443bf780f3c112a586cb3d9901
Project Name: mupdf
License: agpl-3.0
termination: true
*/
typedef struct NNode{
    int h;
    struct NNode * next;
}Node;


Node * initLink(int n){
    Node* head=(Node*)malloc(sizeof(Node));
    head->h=1;
    head->next=0;
    Node* cyclic=head;

    int i;
    for (i=2; i<=n; i++) {
        Node * body=(Node*)malloc(sizeof(Node));
        body->h=i;
        body->next=0;
        cyclic->next=body;
        cyclic=cyclic->next;
    }
    cyclic->next=head;
    return head;
}
Node* findEnd( Node* list )
{
    Node* begin = list;
    while( begin->next != list )
        begin = begin->next;
    return begin;
}

int main()
{
    int num = __VERIFIER_nondet_int();
    if( num <= 0 || num > 65534 )
        return 0;
    Node* list = initLink( num );
    Node* node = list;
    Node* end = findEnd( list );
    float h = 0;
    while( node != end )
    {
        if( node-> h > h )
            h = node -> h;
        node = node->next;
    }
    return 0;
}
