method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    if x >= 0 {
        var y := Double(x);
        r := x + y;
    } else {
        var y := Double(-x);
        r := x + y;
    }
}

method Double(x: int) returns (r: int)
    requires x >= 0
    ensures r == 2 * x
{
    var y := 2 * x;
    r := y;
}