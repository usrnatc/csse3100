lemma IncreasingArray(a: array<int>, n: int)
    requires forall i :: 1 <= i < a.Length ==> a[i-1] < a[i]
    requires 0 <= n < a.Length
    ensures forall i :: n < i < a.Length ==> a[n] < a[i]
    decreases a.Length - n;
{
    if n == a.Length - 1 {

    }
    else {
    IncreasingArray(a, n + 1);
    }
}

method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires true
    ensures true
{

}