/*
Commit Number: 0a8633d07e660813f630e4ab389bb4da9be8bb63
URL: https://github.com/rkd77/elinks/commit/0a8633d07e660813f630e4ab389bb4da9be8bb63
Project Name: elinks
License: GPL2
termination: TRUE
*/
typedef struct Node{
    int size;
    int selected;
}Node;



int main()
{
    Node* menu =(Node*)malloc(sizeof(Node));
    menu->selected = __VERIFIER_nondet_int();
    menu->size = __VERIFIER_nondet_int();
    if( menu->selected <= -2 || menu->size < 1 )
        return 0;
    int pos = menu->selected;
    int direction;
    int action_id =  __VERIFIER_nondet_int();
    if( action_id > 0 && pos >= 1 )
    {
        pos--;
        direction = -1;
    }
    else
    {
        pos++;
        direction = 1;
    }
    pos %= menu->size;
    int start = pos;
    do{
        pos += direction;
        if( pos == menu->size ) pos = 0;
        else if( pos < 0 ) pos = menu -> size - 1;
    }while( pos != start );
    return 0;
}
