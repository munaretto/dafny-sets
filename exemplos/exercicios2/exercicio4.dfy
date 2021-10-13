predicate Sorted(a: array<int>)
reads a
{
    forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

method Main()
{
    var a := new int[3];
    a[0] := 1;
    a[1] := 3;
    a[2] := 5;
    assert Sorted(a);
}