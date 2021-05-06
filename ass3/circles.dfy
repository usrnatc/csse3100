method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires x.Length > 0 && r.Length > 0
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j]
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> (-r[i] != x[j] && r[i] != x[j])
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && (-r[i] == x[j] || r[i] == x[j])
{
    var tempB, tangentMissing, k, l := false, false, 0, 0;
    while k != r.Length && !tempB
        invariant 0 <= k <= r.Length
        invariant tempB ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && (-r[i] == x[j] || r[i] == x[j])
        invariant !tempB ==> forall i, j :: (0 <= i<k && 0 <= j < x.Length) ==> (-r[i] != x[j] && r[i] != x[j])
        decreases r.Length - k
    {
        l:= 0;
        var tangentMissing := false;
        while l != x.Length && !tangentMissing
            invariant 0 <= l <= x.Length
            invariant tempB ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && (-r[i] == x[j] || r[i] == x[j])
            invariant !tempB ==> forall i :: 0 <= i< l ==> (-r[k] != x[i] && r[k] != x[i])
            invariant tangentMissing ==> forall i :: (l <= i < x.Length) ==> (-r[k] != x[i] && r[k] != x[i])
            decreases x.Length - l, !tempB
        {

            if ((-r[k] == x[l] || r[k] == x[l])) {
                tempB := true;
            }
            if (r[k] > 0) {
                if (r[k] < x[l]){
                    tangentMissing := true;
                }
            } else {
                if (-r[k] < x[l]){
                    tangentMissing := true;
                }
            }
            l := l + 1;
        }
        k := k + 1;
    }
    b := tempB;
}