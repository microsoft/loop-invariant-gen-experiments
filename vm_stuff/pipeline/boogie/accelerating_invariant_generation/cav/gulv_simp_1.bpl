procedure main()
{
    var x: int;
    var y: int;
    var unknown1: bool;
    var unknown2: bool;
    var unknown3: bool;

    // Initialization
    x := 0;
    y := 0;

    // Loop body
    while (unknown1)
    invariant x >= 0;
    invariant y >= 0;
    invariant (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 100) ∨ (x = 2 ∧ y = 200);
    {
        havoc unknown1;
        havoc unknown2;
        havoc unknown3;

        if (unknown2) {
            x := x + 1;
            y := y + 100;
        }
        else if (unknown3) {
            if (x >= 4) {
                x := x + 1;
                y := y + 1;
            }
        }
        x := x; // work around VC gen bug
    }

    // Post-condition
    assert(!(x >= 4 && y <= 2));
}