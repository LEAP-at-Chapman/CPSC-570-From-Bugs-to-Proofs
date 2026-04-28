# System specification with TLA+ and PlusCal

```{note}
**Chapter roles (Spring 2026)**  
Author: Jack de Bruyn · Reviewer: Nataniel Farzan  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **TLA+** and **PlusCal** for specifying and reasoning about concurrent and distributed systems.

## Goals

- Explain when TLA+ is an appropriate specification language.
- Walk through a small, runnable example (the Toolbox or command-line workflow).
- Explore a further aspect depending on your interest.
- Link to tutorials, video lectures, and the TLA+ community resources.


## Draft

## Intro

TLA+ is a specification language that is used for modeling systems and programs. TLA+ relies on temporal logic so it is especially useful for systems that are distributed or otherwise rely on concurrency. It exsists at a level of abstraction above the code of a program, so can be a bit challenging for traditionally trained engineers to get into. Using TLA+ is a lot like creating a blueprint for a given system.

TLA+ is best used when you are trying to design a system that is concurrent or otherwise relies on temporality. It can help you to specify, in formal logic rather than informal language, exactly what your system can and should do. From there you can utilize the model checking software TLC to determine whether your program has any logical errors before you've even written it. This will allow you to begin writing your code with a plan in mind that is guaranteed to be logically sound.

Pluscal is a specification language designed for detailing algorithms. It can be used as a more intuitive interface for TLA+ since it more closely resembles a traditional programming langauge and directly transpiles into TLA+. Pluscal is better for sequential algorithms specifically.

The following is a short Pluscal program that defines a one bit clock, taken from the [wikipedia](https://en.wikipedia.org/wiki/PlusCal) page on Pluscal.

```pluscal
-- fair algorithm OneBitClock {
  variable clock \in {0, 1};
  {
    while (TRUE) {
      if (clock = 0)
        clock := 1
      else 
        clock := 0    
    }
  }
}
```

## Example

The following is a Pluscal specification for a mutex lock. Mutex locks are a common structure in programming that can help prevent concurrency errors.

```pluscal
------------------------------ MODULE MutexLock ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N \* Number of processes

ASSUME N \in Nat /\ N > 0

(*
--algorithm Mutex
variables
    lockOwner = 0,          \* 0 means unlocked, otherwise process id
    waiting = [i \in 1..N |-> FALSE],
    inCS = [i \in 1..N |-> FALSE];

process (Proc \in 1..N)
variables self = Proc;
begin Loop:
    while TRUE do

Try:
        waiting[self] := TRUE;

Acquire:
        await lockOwner = 0;
        lockOwner := self;
        waiting[self] := FALSE;

Critical:
        inCS[self] := TRUE;

Exit:
        inCS[self] := FALSE;
        lockOwner := 0;

Remainder:
        skip;

    end while;
end process;
end algorithm;
*)

=============================================================================
```

This code can be copy and pasted into TLC and then converted into TLA+ code. From there, you should be able to run the code and model the mutex lock. You should see that only one process will ever be in the critical zone at a time.
## Case Study

## Further Reasources

- The [TLA+ homepage](https://lamport.azurewebsites.net/tla/tla.html), which contains an overview of the system as well as download links.

- A [Wikipedia article](https://en.wikipedia.org/wiki/TLA%2B). This a good place to start if you would like a basic overview of the language.
