method AssignmentsToMark(students: nat, tutors: nat) returns (r: nat)
    requires students > 0 && tutors > 1
    ensures r < students
{
    r := students / tutors;
    DivisionLemma(students, tutors);
}

lemma DivisionLemma(n: nat, d: nat)
    requires n > 0 && d > 1
    ensures n/d < n
{
    if n ==1 { } // Dafny verifier can already prove this (base) case without any help
    else {
        DivisionLemma(n/n,d);
    }
}