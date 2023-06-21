procedure main()
{
    var idBitLength: int;
    var material_length: int;
    var nlen: int;
    var j: int;
    var nondet: bool;

    // pre-conditions
    assume(nlen == idBitLength div 32);

    // initialization
    j := 0;

    // loop body
    while (nondet)
    invariant 0 <= j;
    invariant (j < idBitLength div 8 && j < material_length) || (j >= idBitLength div 8 || j >= material_length);
    {
        havoc nondet;
        // assertions
        assert(0 <= j);
        assert(j < material_length);
        assert(0 <= j div 4);
        assert(j div 4 < nlen);

        // increment j
        j := j + 1;
    }

    // post-conditions
    assert(0 <= j);
    assert(j >= idBitLength div 8 || j >= material_length);
}