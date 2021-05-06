method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires r.Length != 0 && x.Length != 0
    ensures (b ==> exists i, j :: (0 <= i < r.Length && 0 <= j < x.Length) && (-r[i] == x[j] || r[i] == x[j])) || (!b ==> forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) && (-r[i] != x[j] && r[i] != x[j]))
{
    var m, n , tempB := 0, 0, false;
    
    while m < r.Length && !tempB
        invariant 0 <= m <= r.Length
        invariant tempB ==> exists i, j :: (0 <= i < r.Length && 0 <= j < x.Length) && (-r[i] == x[j] || r[i] == x[j])
        decreases r.Length - m
    {
        n := 0;
        while n < x.Length && !tempB
            invariant 0 <= n <= x.Length
            invariant tempB ==> exists i, j :: (0 <= i < r.Length && 0 <= j < x.Length) && (-r[i] == x[j] || r[i] == x[j])
            decreases x.Length - n, !tempB
        {
            if (-r[m] == x[n] || r[m] == x[n]) {
                tempB := true;
            }
            n := n + 1;
        }
        m := m + 1;
    }
    b := tempB;
}