abstract sig Object {}
sig File extends Object {}

sig Dir extends Object {
	entries : set Entry
}


sig Entry {
  name : one Name,
  object : one Object
}

sig Name {}

one sig Root extends Dir {}

fact {
  // Entries cannot be shared between directories #1
  all x, y : Dir | x != y implies no (x.entries & y.entries)
}

fact {
  // Entries cannot be shared between directories #2
  all disj x, y : Dir | no (x.entries & y.entries)
}

fact {
  // Entries cannot be shared between directories #3
  all e : Entry | lone entries.e
}

fact {
  // Entries cannot be shared between directories #4
  entries in Dir lone -> Entry
}

fact {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.entries & name.n)
}

fact {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone object.d
}

fact {
  // Every object except the root is contained somewhere
  Entry.object = Object - Root
}


run example {
  some File
  some Dir - Root
} for 4
