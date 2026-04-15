// methods

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less <= x <= more // postcondition
  requires 0 <= y
  // Why does this fail?
{
  more := x + y;
  less := x - y;
}

method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
{
  if a <= b {
    return b;
  } else {
    return a;
  }

}

method m()
{
  // local variables support type inference
  var x, y, z := 1, 2, true;
}

method Abs(x: int) returns (y: int)
  ensures 0 <= y && (y == x || y == -x)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  } 
}

// testing Abs
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  assert v == 3; // why does this fail?
}

// Functions

function abs(x: int): int
{
  if x < 0 then -x else x
}
method testabs()
{
  assert abs(3) == 3;
}

// Loop invariants

method inc1(n: nat)
{
  var i: int := 0;
  while i < n
   invariant 0 <= i <= n
  {
    i := i + 1;
  }
  assert i == n; // why does this fail?
}

function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

// Termination

method decrease()
{
  var i := 20;
  while 0 < i
    invariant 0 <= i
    decreases i
  {
    i := i - 1;
  }
}

method decrease2()
{
  var i, n := 0, 20;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}

// Proving correctness

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}

// Predicates and frames

predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}


// Lemmas


lemma SkippingLemma(a: array<int>, j: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  requires 0 <= j < a.Length
  ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[j] - (i-j) <= a[i]
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
  {
    i := i + 1;
  }
}


method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
{
  index := 0;
  while index < a.Length
    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
  {
    if a[index] == 0 { return; }
    
    SkippingLemma(a, index);
    index := index + a[index];
  }
  index := -1;
}
