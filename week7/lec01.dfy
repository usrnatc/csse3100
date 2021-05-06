method LinearSearch0<T>(a: array<T>, P:T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        decreases if n <= a.Length then a.Length - n else n - a.Length
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
}

method LinearSearch1<T>(a: array<T>, P:T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures forall i :: 0 <= i < n ==> !P(a[i])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
}

method LinearSearch3<T>(a: array<T>, P:T -> bool) returns (n: int)
    requires exists i :: 0 <= i < a.Length && P(a[i])
    ensures 0 <= n < a.Length && P(a[n])
{
    n := 0;
    while true
        invariant 0 <= n < a.Length
        invariant exists i :: n <= i < a.Length && P(a[i])
        decreases a.Length - n
    {
        if P(a[n]) {
            return;
        }
        n := n + 1;
    }
}


method min(a: array<int>) returns (m: int)
    requires a.Length > 0 
    ensures exists i :: 0 <= i < a.Length && m == a[i]
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{
    var n := 0;
    m := a[0];
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> m <= a[i]
        invariant exists i :: 0 <= i < a.Length && m == a[i]
    {
        if a[n] < m {
            m := a[n];
        }
        n := n + 1;
    }
}

