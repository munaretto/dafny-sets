method FindMaxValue(a:array<int>) returns (m:int)
requires a.Length > 0
//m é um elemento do array
ensures exists i :: 0 <= i < a.Length && a[i] == m
//m é o maior elemento
ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
{
    var index := 0;
    m := a[index];
    while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] <= m
    invariant index == 0 ==> a[0] == m
    invariant index > 0 ==> exists i :: 0 <= i < index && a[i] == m
    {
        if a[index] > m
        {
            m := a[index];
        }
        index := index + 1;
    }
}
