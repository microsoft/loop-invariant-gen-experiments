 procedure main()
{
    var x: int;
    var size: int;
    var y: int;
    var z: int;

    x := 0;

    while (x < size)
        invariant x <= size && (x == 0 || z >= y)
    {
        x := x + 1;
        if (z <= y)
        {
            y := z;
        }
    }

    if (size > 0)
    {
        assert(z >= y);
    }
}