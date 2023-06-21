procedure main()
{
    var x: int;
    var c: bool;
    var unknown_int: int;
    var unknown_bool: bool;

    // pre-condition
    x := unknown_int;
    assume(x >= -2147483648 && x <= 2147483647); // x can have any integer value

    // loop body
    while (x > 0)
    invariant x >= 0; // loop invariant
    {
        c := unknown_bool;
        assume(c == true || c == false); // c can be either true or false

        if (c) {
            x := x - 1;
        } else {
            x := x - 1;
        }
    }

    // post-condition
    assert(x == 0);
}