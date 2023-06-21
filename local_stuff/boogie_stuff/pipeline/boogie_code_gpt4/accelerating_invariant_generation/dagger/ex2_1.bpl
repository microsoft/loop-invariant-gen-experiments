procedure main()
{
    var x: int;
    var nondet: bool;

    // pre-conditions
    x := 0;

    // series of conditional statements
    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 22; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 20; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 18; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 16; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 14; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 12; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 10; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 8; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 6; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 4; }

    havoc nondet;
    if (nondet) { x := x + 1; }
    else { x := x + 2; }

    // post-condition
    assert(x <= 132);
}