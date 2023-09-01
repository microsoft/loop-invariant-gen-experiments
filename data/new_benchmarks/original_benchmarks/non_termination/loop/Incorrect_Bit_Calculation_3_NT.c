/*
Commit Number: 5bec3fff0bac50f4b4d4d3b02e70161a2bf38d0f
URL: https://github.com/brltty/brltty/commit/5bec3fff0bac50f4b4d4d3b02e70161a2bf38d0f
Project Name: brltty
License: LGPL-2.1
termination: false


This program will go into an infinite loop if wc is negative


*/
int main()
{
    int wc = __VERIFIER_nondet_int();
    do{
        //loop;
    }while( wc >>= 6 );
    return 0;
}
