method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires s - m <= m
    ensures s == x + y
    ensures (m == x || m == y) && x <= m && y <= m
{
<<<<<<< HEAD
    if ()
=======
    y := m;
    x := s - m;

    return x, y;
>>>>>>> 24e6fb2f20b9d34a040022072734e60c81357109
}