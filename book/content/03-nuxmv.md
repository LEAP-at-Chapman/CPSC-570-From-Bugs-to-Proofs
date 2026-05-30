# Model checking with nuXmv and NuSMV

```{note}
**Chapter roles (Spring 2026)**  
Author: Michael Smith · Reviewer: John Mulhern  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **nuXmv** (and the related **NuSMV** lineage) for finite- and infinite-state model checking.

## Goals

- Summarize the CTL / LTL verification workflow at a high level.
- Include a compact SMV-style model with a non-trivial property.
- Explore a further aspect depending on your interest.
- Link to tool manuals.

## Draft

# Symbolic Model Verification
Another important aspect of the formal verification of systems is model construction and checking. This chapter introduces one particular model-checker, NuSMV, and an extension, NuXMV. The basic idea behind symbolic model checkers is to use some specification that describes a particular system to build many different representations of it (models), often in the form of state-transition graphs. If the model checker is able to produce a model that obeys the transitions/state changes but ultimately breaks some of the rules set out in our specification (counterexample), then we have concrete evidence that either our formal description of our system is inadequate or the rules we are applying are too strict for our system. Whatever the case, this is a clear indication that there is flawed thinking within our design. Alternatively, if the model checker builds many models and fails to produce a counterexample, then we have strong evidence that our design will obey the propositions within our specification and behave as expected. The following goes further in depth into each of these components of model verification. 

## Making a model

To use model checkers, we need to consider the individual attributes that change within our system (variables). The different possible values that can be assigned to these variables can be represented as states. Once we define how each variable transitions from one value/state to another and the conditions necessary for that to happen, the model checker will be able to use this as a blueprint to build variations of models that obey these transition rules. It is these models that we will check against the expected inherent rules of our design. Here is an example of this done in NuSMV:

```code
VAR
  train : {absent, approaching, near, crossing, leaving};
  gate  : {up, lowering, down, raising};

ASSIGN
  -- Train transitions (given — do not modify)
  init(train) := absent;
  next(train) := case
    train = absent      : {absent, approaching};
    train = approaching : near;
    train = near        : crossing;
    train = crossing    : leaving;
    train = leaving     : absent;
  esac;

  -- Gate: starts in the up position (given)
  init(gate) := up; 

  -- TODO: Complete the gate transitions.
  -- Replace the FALSEs with the correct guards.
  next(gate) := case
    train = approaching   : lowering;   -- When should the gate start lowering?
    gate = lowering       : down;       -- When is lowering complete?
    train = leaving       : raising;    -- When should the gate start raising?
    gate = raising        : up;         -- When is raising complete?
    TRUE                  : gate;       -- Default: stay in current position
  esac;
```

## Temporal Logic

After specifying all state transitions, we are ready to put our design rules to the test. The language in which we express these rules is temporal logic, writing these rules as unambiguous mathematical formulas. In particular, we leverage two sublogics: [Linear Temporal Logic](https://en.wikipedia.org/wiki/Linear_temporal_logic) (LTL) and [Computation Tree Logic](https://en.wikipedia.org/wiki/Computation_tree_logic) (CTL), which we discuss in more detail later. This allows us to make propositions like “This property always holds”, “Eventually, this property holds”, or “This property could hold”. A practical example of this is making statements like “There will always be no more than one train crossing an intersection at a time” or “It is always the case that I will eventually receive a packet from the server”. With examples like these in mind, it quickly becomes obvious how model checkers can be tremendously helpful when designing on the conceptual level, as these models do not need to be language-specific. Some general properties that we can express include fairness, liveness, and atomicity. Here is an example of these types of specifications [See the LTL, CTL, NuSMV sections for clarity](#basic-theory):

```code
LTLSPEC G safe 
LTLSPEC G ((train = approaching) -> F (gate = down))
SPEC EF (train = crossing & gate = down)
SPEC AG (EF (gate = up))
```

## State Space and Counterexamples

Once we have defined our transitions and expressed the rules we believe our system should follow in temporal logic, the model checker can either accept or reject each proposition. It accomplishes this by representing all possible states or combinations of states, either explicitly or implicitly. If the model checker is unable to produce a state that violates a proposition, then the system satisfies that property. However, if the model checker can produce a state that violates the proposition, then we know that the property does not hold, and the model checker will generate a model demonstrating how this state was reached, which is referred to as a counterexample. This is particularly helpful when attempting to debug, since it can reveal subtle mistakes within the structure of the system. 

# Basic Theory

To further understand how the model checker does verification, we must understand Linear Temporal Logic (LTL) and Computation Tree Logic (CTL). 

## LTL

In LTL, we apply logic over sequences of states or paths. From a high level, a system is defined as having a set of states, some of which are initial states, transitions between the states (and corresponding actions/triggers), and a set of propositions that are mapped to true or false depending on whether they are satisfied in each state. In addition to basic logical operators like conjunction, negation, etc., we have temporal operators, the most common of which are next, until, eventually, and always. We can create propositions like the conceptual ones listed above through different combinations of these operators. Each path is one sequence of states, each with their corresponding set of true and false basic propositions. Paths can be finite or infinite, however, they must end in a terminal state if they are to be finite and still maximal. Maximal refers to the idea that the path/computation does not spontaneously halt in a state that the model could potentially move on from based on transition rules. In order for a system to satisfy a proposition, all maximal paths from all initial states must satisfy the proposition. 

## CTL

CTL works similarly but instead of applying logic over individual linear paths, we apply it over branching paths based on which states we are able to visit according to our transition rules. Due to this, we use quantifiers such as “for all paths” or “there exists a path”. While LTL and CTL appear quite similar, there are some propositions that each can express that the other cannot. 

## NuSMV

NuSMV permits the use of both LTL and CTL formulas, enabling us to check a wider range of potential properties than either sublogic would be able to provide alone. Here is the corresponding NuSMV syntax for the previously mentioned operators:

### Logical Operators

| Meaning       | Mathematical Syntax | nuSMV Syntax |
| ------------- | ------------------- | ------------ |
| True          | ⊤                   | `TRUE`       |
| False         | ⊥                   | `FALSE`      |
| Negation      | ¬p                  | `!p`         |
| And           | p ∧ q               | `p & q`      |
| Or            | p ∨ q               | `p \| q`     |
| Implies       | p → q               | `p -> q`     |
| Biconditional | p ↔ q               | `p <-> q`    |
| Equality      | x = y               | `x = y`      |
| Not equal     | x ≠ y               | `x != y`     |

### LTL Operators

| Meaning           | Mathematical Syntax | nuSMV Syntax |                      Explanation                                         | 
| ----------------- | ------------------- | ------------ | ------------------------------------------------------------------------ |
| Proposition       |   p                 | `p`          | This propostion (`p`) holds at the current (first) state in the sequence |
| Next              |   ◯ p              | `X p`        | p holds in the next state in the sequence                                |
| Eventually        |   ◇ p              | `F p`        | p holds for at least one future state in the sequence                    |
| Globally / Always |   □ p               | `G p`        | p holds for the entire sequence                                          |
| Until             |   p   U   q         | `p U q`      | p holds for all states in the sequence up to the state where q holds     |
| Release           |   p   R   q         | `p R q`      | q holds up to and including the state where p holds for the first time   |



### CTL Path Quanitifiers

| Meaning             | Symbol | nuSMV Syntax |
| ------------------- | ------ | ------------ |
| For all paths       | ∀      | `A`          |
| There exists a path | ∃      | `E`          |


To get a better idea, let us look at an example. Below is a simple representation of an elevator system in NuSMV syntax. You will notice each of the parts pointed out in the Idea of Model Checking section of this chapter (signified by VAR, ASSIGN, and SPEC): 

# Example of NuSMV Model

```code
MODULE main

VAR
    elevator_position   : 1..3;
    elevator_doors      : {opened, closed};
    elevator_direction  : {up, down, resting};
    
    f1_call             : boolean;
    f2_call             : boolean;
    f3_call             : boolean;


ASSIGN

    init(elevator_position) := 1;
    init(elevator_doors)    := closed;
    init(elevator_direction) := resting;
    init(f1_call)           := FALSE;
    init(f2_call)           := FALSE;
    init(f3_call)           := FALSE;

    next(elevator_position) :=
        case
            elevator_direction = up 
            & elevator_position < 3     : elevator_position + 1;
            
            elevator_direction = down 
            & elevator_position > 1     : elevator_position - 1;
            
            TRUE                        : elevator_position;
        esac;
    

    next(elevator_doors) :=
        case
            (elevator_position = 1 & f1_call) |
            (elevator_position = 2 & f2_call) |
            (elevator_position = 3 & f3_call) : opened;
        
            TRUE : closed;
        esac;

    next(elevator_direction) :=
        case 
            (elevator_position = 1 & f1_call)               : resting;
            (elevator_position = 2 & f2_call)               : resting;
            (elevator_position = 3 & f3_call)               : resting;

            (elevator_position = 1 & (f2_call | f3_call))   : up;
            (elevator_position = 2 & f3_call)               : up;

            (elevator_position = 3 & (f1_call | f2_call))   : down;
            (elevator_position = 2 & f1_call)               : down;

            
            TRUE                                            : resting;
        esac;


    next(f1_call) :=
        case
            elevator_position = 1 & elevator_doors = opened : FALSE;
            f1_call = TRUE : TRUE;
            TRUE                                            : {TRUE, FALSE};
        esac;

    next(f2_call) :=
        case
            elevator_position = 2 & elevator_doors = opened : FALSE;
            f2_call = TRUE : TRUE;
            TRUE : {TRUE, FALSE};
        esac;

    next(f3_call) :=
        case
            elevator_position = 3 & elevator_doors = opened : FALSE;
            f3_call = TRUE : TRUE;
            TRUE : {TRUE, FALSE};
        esac;
DEFINE

bounded := (elevator_position >= 1 & elevator_position <= 3);

safe := (elevator_direction != resting -> elevator_doors = closed);

Call_1_Served := (elevator_position = 1 & elevator_doors = opened);
Call_2_Served := (elevator_position = 2 & elevator_doors = opened);
Call_3_Served := (elevator_position = 3 & elevator_doors = opened);

SPEC AG bounded
SPEC AG safe
LTLSPEC G (f1_call -> F (Call_1_Served))
LTLSPEC G (f2_call -> F (Call_2_Served))
LTLSPEC G (f3_call -> F (Call_3_Served))
```

In this elevator example, we have a couple of specifications that we would want to hold true in a real-world system. In this case, "safe" represents the concept that "if the elevator is moving then the doors must be closed". We would want this guarantee of safety for passengers to always be the case. Thus, by specifying the CTL formula that all states along all branches must uphold this property, we can either identify states where passengers could be at risk or ensure that scenario is never possible within the scope of our system. Similarly, there are also specifications depicted here relating to guarantees about service such as "if I call for the elevator, it must come to me eventually". 

## Improvements of nuXmv

NuXmv is an extension of NuSMV with the most notable difference being that we can now model infinite state transition systems. This functionality was implemented by adding two new types, `real` and `integer`, as well as a suite of new algorithms for both finite and infinite state systems. This is particularly helpful in many realistic applications where our model is not bounded. Some examples of this include when our model includes unbounded arrays or other data structures. However, NuXmv has the tradeoff that it no longer supports asynchronous systems. 

# History of NuSMV

## Foundations of Model Checking

At the foundation of model checking are [Kripke structures](https://en.wikipedia.org/wiki/Kripke_structure_(model_checking)). The labelled state transition graph pictured above is one such example of a Kripke structure. These graphs were proposed in the 1950s as a means of representing system behaviors with the intent of applying them to manual proof checking and verification. 

By the 1970s, LTL and CTL were introduced and deemed efficient ways of expressing desirable properties and constructing proofs to formally verify these properties, making them ideal for applications in computer science and systems engineering. 

In the early 1980s, it was proposed that, rather than developing proofs by hand, the entire state space of finite-state systems could be explored by a computer, providing an even easier method of verification. This is when the notion of modern model checking started to take shape. The only issue with this approach was the “state explosion problem”. This refers to the exponential growth of the state space as the number of variables within a system increases, making automated verification no longer a viable option after a certain point. One solution to this is [Binary Decision Diagrams](https://en.wikipedia.org/wiki/Binary_decision_diagram)(BDDs), which allow for the symbolic representation of state spaces. By removing the need to explicitly create every possible state, automation remains a useful tool in verification. 

## SMV1, NuSMV, and nuXmv

Symbolic Model Verifier (SMV) became the first BDD-based automated model checker in 1990 as a result of PhD research at Carnegie Mellon University. While being the first of its kind, it still had many limitations. 
In 1999, NuSMV was created: a complete redesign and extension of SMV with such additions like LTL and the intention of being open-source. Two years later, NuSMV2 was released, introducing an alternative means of symbolic representation: propositional satisfiability (SAT). 
In 2014, nuXmv extended NuSMV further by adding new SAT and Satisfiability Modulo Theory-based (SMT) verification algorithms and permitting infinite-state models. NuXmv has been used in various projects, such as [Electrum](https://haslab.github.io/Electrum/), [Kratos](https://es.fbk.eu/index.php/tools/kratos/), [OCRA](https://ocra.fbk.eu/), [xSAP](https://xsap.fbk.eu/), [etc.](https://nuxmv.fbk.eu/tools-using-nuxmv.html), since then. 

# Tool Pages and User Manuals

Bozzano, M., Cavada, R., Cimatti, A., Dorigatti, M., Griggio, A., Mariotti, A., Micheli, A., 
    Mover, S., Roveri, M., & Tonetta, S. (n.d.). NUXMV 2.1.0 User Manual. 
    nuxmv.fbk.eu. https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf

Cavada, R., Cimatti, A., Jochim, C. A., Keighren, G., Olivetti, E., Pistore, M., Roveri, M., 
    & Tchaltsev, A. (n.d.). NuSMV 2.7.0 User Manual. 
    https://nusmv.fbk.eu/userman/v27/nusmv.pdf

NuSMV home page. (n.d.). Retrieved May 27, 2026, from https://nusmv.fbk.eu/ 

nuXmv—Home. (n.d.). Retrieved May 27, 2026, from https://nuxmv.fbk.eu/ 