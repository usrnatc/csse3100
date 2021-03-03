method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    if x >= 0 {
        var y := Double(x);
        r := x + y;
    } else {
        var y := Double(-x);
        r := x + y; // Should be r := x - y; for this program to hold
    }
}

method Double(x: int) returns (r: int)
    requires x >= 0
    ensures r == 2 * x