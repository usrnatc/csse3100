function method More(x: int) : int {

    if x <= 0 then 1 else More(x -2) + 3
}

lemma {:induction false} Increasing(x: int)
    ensures x < More(x)
{
    if x <= 0 {
        calc == {
            x;
            <= 0;
            < 1;
            More(x);
        }
    }
    else {
        calc {
            true;
            ==> {Increasing(x - 2);} x - 2 < More(x - 2);
            <==> x + 1 < More(x - 2) + 3;
            <==> x + 1 < More(x);
            ==> x < More(x);
        }
    }
}


function Reduce(m: nat, x: int): int {
    if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
    ensures Reduce(m, x) <= x
{
    if m == 0 {

    } else {
        calc {
            Reduce(m, x);
            == Reduce(m / 2, x + 1) - m;
            <= {ReduceUpperBound(m / 2, x + 1);
                assert Reduce(m / 2, x + 1) <= x + 1;} x + 1 - m;
            <= {assert m > 0;} x;
        }
    }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
    ensures x - 2 * m <= Reduce(m, x)
{
    if m == 0 {

    } else {
        calc {
            Reduce(m, x);
            == Reduce(m / 2, x + 1) - m;
            >= {ReduceLowerBound(m / 2, x + 1);
                assert x + 1 - 2 * (m / 2) <= Reduce(m / 2, x + 1);}
                x + 1 - 2 * (m / 2) - m;
            >= {assert 2 * (m/2) <= m;} x + 1 - m - m;
            == x + 1 - 2 * m;
            > x - 2 * m;
        }
    }
}
