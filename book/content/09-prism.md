# Probabilistic model checking with PRISM

```{note}
**Chapter roles (Spring 2026)**  
Author: Anela Quiroz · Reviewer: Kalin Richardson  
See [Chapter assignments](0-chapter-assignments.md).
```

This chapter introduces **PRISM** for modeling and analyzing systems with probabilistic or stochastic behavior.

## Goals

- Contrast discrete-time and continuous-time Markov models at a high level.
- Present a small PRISM model with a quantitative property (reachability reward, steady-state, etc.).
- Explore a further aspect depending on your interest.
- Link to the PRISM manual, case studies, and benchmark suites.

## 1. Idea

Probabilistic model checking is a formal verification technique for establishing the correctness, performance, and reliablility of systems that exhibit stochastic behavior. A precise mathematical model of a real-life system is constructed first, then formal specifications of properties are automatically analyzed against it. The exploration is exhaustive and combines graph-theoretic algorithms with numerical methods. 

Unlike classical model checking, which asks *"can this bad state be reached?"*, probabilistic model checking asks:

- *With what **probability** does an attack succeed?*
- *What is the **expected number of steps** to crack a PIN?*
- *What is the **optimal strategy** for an adversary — or a defender?*

PRISM has been applied across many domains, inculding communication and multimedia protocols, randomized distributed algorithms, security protocols, and biological systems. 

The case study in this chapter, PIN cracking in banking ATM netowrks, illustrates how PRISM handles a real-world security scenario using Markov Decision Proccesses (MDPs)

## 2. Basic Theory 

There are different types of probabilistic models PRISM can build and analyze:

| Model | Time       | Nondeterminism    | Use Case                              |
|-------|------------|-------------------|---------------------------------------|
| DTMC  | Discrete   | No                | Randomized protocols, games           |
| CTMC  | Continuous | No                | Performance, reliability              |
| MDP   | Discrete   | Yes               | Concurrent or adversarial systems     |
| PTA   | Continuous | Yes               | Real-time systems with clocks         |
| POMDP | Discrete   | Yes (partial obs) | Planning under uncertainty            |
| POPTA | Continuous | Yes (partial obs) | Real-time systems with hidden state   |

### 2.1 Discrete-Time Markov Chains (DTMCs)

A **Discrete-Time Markov Chain (DTMC)** model a system that transitions between states at each step, with each transition governed by a fixed probability. Formally, a DTMC is a tuple $(S, s_0, P, L)$ where:

- $S$ is a finite set of states,
- $s_0 \in S$ is the initial state,
- $P : S \times S \to [0,1]$ is a transition probability matrix, where $\sum_{s' \in S} P(s, s') = 1$ for all $s$,
- $L : S \to 2^{AP}$ is a labeling function over atomic propositions.

The key property is the **Markov property**: the probability of transitioning to the next state depends only on the current state, not on any histroy of previous states. This memoryless makes DTMCs tractable for automated analysis.

A simple example: a cluent repeatedly attemps to send a message. At each step, transmission succeeds with probability $p$ and fails with probability $1 - p$. This gives a two-state DTMC with self-loop on failure and an absorbing accepting state on success. The expected number of attempts is $1/p$, which PRISM can compute exactly.

### 2.2 Continuous-Time Markov Chains (CTMCs)

A **Continuous-Time Markov Chain (CTMC)** extends the DTMC idea to setting where transitions do not happen at uniform discrete ticks, but instead occur after exponentially disrupted delay. Each transition from state $s$ to state $s'$ is labeled with a **rate** $\lambda_{s,s'} > 0$. The time spent in state $s$ before any transition fires is exponenially distributed with rate $\sum_{s'} \lambda_{s,s'}$.

CTMCs are the powerhouse model for performance analysis and reliability engineering:

- *How long does the server stay available before a failure?*
- *What is the stead-state probability of the netowrk being overloaded?*
- *What fraction of time is a component in a degraded state?*

PRISM analyzes CTMCs using **Continuous Stochastic Logic (CSL)** which extends PCTL with time-bounded reachability and steady-state operators appropriate for continuous time.

### 2.3 Markov Decision Processes (MDPs)

When a system invovles both probabilisitc choices **and** nondeterministic choices:

For example, an adversary who picks the best possible attack. A plain Markov chain is insufficient. A **Markov Decision Process** augments a STMC with nondeterminism: in each state, an agent (scheduler, adversary, or protocol participant) chooses and action, and that action triggers a probability distribution over successor states.

MDPs allow PRISM to answer questions of the form

- *What is the **maximum** probability of reaching a failure state, over all possible adversary strategies?*
- *What is the **minimum** expected number of steps to complete, regardless of environment behavior?*

PRISM computes these bounds using value iteration and policy iteration over the MDP, returning both the optimal value and the optimal policy (stratefy) that achieves it.

### 2.4 Property Specification

PRISM uses a unified property specification language that incorporates several probabilistic temporal logics, most importantly:

- **PCTL** (Probabilistic Computation Tree Logic) - for DTMCs and MDPs
- **CSL** (Continuous Stochastic Logic) - for CTMCs
- **LTL / PCTL\*** - for more expressive path properties

The central operator is the **P operator**:

```
P bound [ path_proberty ]
```

where 'bound' is a comparison like `>=0.99` or `<=0.01`, and `path_property` is a temporal formula over the model's states. For example:

```
// Is the probability of eventually cracking the PIN at least 0.8?
Pmax>=0.8 [ F pin_cracked ]

// What is the exact maximum probability of cracking within 50 steps?
Pmax=? [ F<=50 pin_cracked ]
```
The **R operator** handles *reward* (or cost) based properties, allowing PRISM to compute expected cumulative costs or expected time:

```
//What is the expected number of queries until the PIN is revealed?
Rmin=? [ F pin_cracked ]
```

The **S operator** computes steady-state probabilities for CTMSs:

```
//In the long run, is the probability of server overlaod below 1%?
S<=0.01 [ overloaded ]
```

PRISM accepts both *verification* queries (does the model satisfy this bound?) and *quantitative* queries (what is the actual value?). The quantitative form uses `=?` in place of a comparison bound and is often the more informative choice. 

--- 

## 3 The PRISM Language

PRISM models are written in a **reactive modules** style: the system is broken into a set of synchronizing modules, each owning a set of typed variables, and behavior is described by guarded commands.

### 3.1 Modules and Variables

```prism
mdp

module Attacker
    guess : [0...9] init 0; // the attacker's current PIN guess
    done : bool init false;

    // Attacker nondeterministically chooses a digit to try
    [] !done -> (guess'=0);
    [] !done -> (guess'=1);
    // ... (commands for digits 2-9 omitted for brevity)
endmodule
```

Each line inside the module is a **command** of the form:

```
[action] guard -> prob_update;
```

- The optional `[action]` label enables synchronization between modeules.
- The `guard` is a Boolean expression over the modules's variables.
- The `prob_update` is a probabilistic update: `p1:(updates) + p2:(updates) + ...`, where the probabilities sum to 1.

### 3.2 A minimal DTMC Example: Randomized Self-Stabilization

The follwoing model encodes a simple randommized protocol where a node probabilistically flips its state until the system stabilizes:

```prism
dtmc

module Node 
    s : [0..2] init 0;
    // s=0: unstable, s=1: stabilizing, s=2: stable

    [] s=0 -> 0.5:(s'=1) + 0.5:(s'=0);
    [] s=1 -> 0.8:(s'=2) + 0.2:(s'=0);
    [] s=2 -> (s'=2);
endmodule

rewards "steps"
    s<2 : 1;
endrewards
```

With this model, we can ask:

```
// Expected steps to reach stable state
R{"steps"}=? [ F s=2 ]
```

### 3.3 Constants, Formulas, and Labels

PRISM provides several mechanisms to keep models manageable:

- **Constants** (`const int N = 4;`) for parameterized models
- **Formulas** (`formula active = (s>0 & !done);`) for derived Boolean expressions
- **Labels** (`label "success" = (s=2);`) for naming sets of states to reference in properties

```prism
const int PIN_LENGTH = 4;
const int MAX_GUESSES = 3;

formula locked = (attemps >= MAX_GUESSES);
label "cracked" = (pin_found = true);
label "locked_out" = locked;
```

---

## 4. Case Study: PIN Cracking Schemes

This case study is drawn from real-world research on the security of ATM banking networks, contributed to the PRISM case study library by Graham Steel. The full model files are available at the [PRISM PIN Cracking case study page](https://www.prismmodelchecker.org/casestudies/pincracking.php).

### 4.1 Background: ATM Netowrks and HSMs

Suppose a customer banks in the UK and uses their card at an ATM in Germany. The types PIN must travel encrypted across the international network to reach the issuing bank for authorization. Because different netowrk nodes use differnt encryption keys, the PIN is decrypted and re-encrypted at each intermediate node.

Exposing a PIN as plaintext in the memory of an ordinaty computer is considered an unacceptable security risk. All PIN processing therefore takes place inside **Hardware Security Modeules (HSMs)**. They are physically tamper-proof devices with a shielded enclosure housing a CPU, a dedicated cryptoprocessor, and a small amount of memory. If an intruder attempts to open the casing or inserts probes, the device auto-erases its memory in nanoseconds. The IBM 4758 is one well-known example.

The HSM exposes a strictly controlled API whose goal is to prevent even corrupt bank insiders from learning customer PINs. However, in recent research, it has shown that the API itself can be turned against its purpose.

### 4.2 PIN Block Formats

To be encrypted by algorithms such as 3DES, a PIN must first be packed into a 64-bit **PIN block**. Different banks use differnt formats.

**VISA-3 format** (for a 4-digit PIN):

```
P1 P2 P3 P4 F F F F F F F F F F F F
```

Each character is a 4-bit nybble. `P1`-`P4` are the PIN digits and `F` is the hex value F. A drawback of this format is that two customers with the same PIN produce the same encrypted block under the same key.

**ISO-0 format** (from ISO standard 9564) address this by XORing the PIN block against the customer's account number:

```
B1 = 0  4  P1 P2 P3 P4 F  F  F  F  F  F  F  F  F  F
B2 = 0  0  0  0  A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12
PIN Block = B1 XOR B2
```

The leading `0` in `B1` marks the format; `4` indicated PIN length. `A1`-`A12` are the 12 digits of the customers Personal Account Number (PAN). Two customers with the same PIN now produce different encrypted blcoked, since their PANs are different.

### 4.3 The Reformatting Attack

THe HSM API typically includes a **translate** command that reformats a PIN block from one format to another. This is necessary when the block passes between nodes expecting different formats. To translate from ISO-0 to VISA-3, the user must re-supply the PAN so the HSM can XOR it away and recover `B1`. Before doing so, the HSM performs an error check: it verifies that all recovered PIN digits are decimal (0–9) rather than hexadecimal (A–F).

This check is the vulnerability. Suppose an attacker supplies a *modified* PAN, specifically with the first account digit XORed against 8: $A_1' = A_1 \oplus 8$. When the HSM XORs this against the encrypted block to recover digit `P3`:
 
- If `P3` is 0, 1, 8, or 9, then `P3 XOR 8` remains decimal — the check **passes**, silently.\
- If `P3` is in the range 2–7, then `P3 XOR 8` falls in the hexadecimal range A–F — the HSM **signals an error**.

The error signal reveals a constraint on the unknown PIN digit: a pass tells the attacker that `P3 ∈ {0, 1, 8, 9}`, and an error tells them `P3 ∈ {2, 3, 4, 5, 6, 7}`. By repeating this process with different XOR values, the attacker progressively narrows the candidate set. Each pair of digits (0 and 1, 2 and 3, etc.) yields identical error patterns, so the attacker can narrow each digit down to a pair but not yet to a unique value. By then masquerading the ISO block as a VISA-3 block to shift the PIN digits' positions, the attack can be extended to determine each digit uniquely.

### 4.4 AnaBlock and the MDP Model

There are several known families of PIN recovery attacks, and each HSM customer configures their device differently — enabling different PIN block formats and different API commands. The tool **AnaBlock**, built using constraint logic programming in SICStus Prolog, takes an HSM configuration and automatically determines the most effective available attack. It does this by building a large tree of all possible attacker moves:
 
- For a **single attack**, the tree's edges represent only probabilistic outcomes (the HSM's error-or-pass response). The resulting model is a Markov chain (MC).
- For a **family of attacks**, the tree contains both probabilistic outcomes *and* nondeterministic choices (which command the attacker issues next). The resulting model is a **Markov Decision Process (MDP)**.
PRISM then analyzes the MDP to identify the Markov chain within it that represents the most effective attack — either the one that determines the PIN in the fewest expected steps, or, when no complete recovery is possible, the one that reduces the PIN to the fewest remaining candidates.
 
Each **state** in the model encodes the attacker's current knowledge: a set of Boolean flags recording which digit values are still possible. The initial state has all ten digits possible for each position; a final state has each digit uniquely determined.

### 4.5 The PRISM Model

Below is the auto-generated PRISM fragment for digit 3, corresponding to the tree fragment in the AnaBlock paper. The module tracks which of the ten possible values (0-9) for PIN digit 3 remain consistent with the HSM's responses so far.

```prism
// Model for PIN Block attack analysis
// Auto generated by AnaBlock
// Author G. Steel, Aug 2005
 
mdp
 
module M1
 
  P3_could_be0 : bool init true;
  P3_could_be1 : bool init true;
  P3_could_be2 : bool init true;
  P3_could_be3 : bool init true;
  P3_could_be4 : bool init true;
  P3_could_be5 : bool init true;
  P3_could_be6 : bool init true;
  P3_could_be7 : bool init true;
  P3_could_be8 : bool init true;
  P3_could_be9 : bool init true;
  P3_guessed   : bool init false;
 
  PIN_Digit3 : [0..10] init 10;   // 10 = digit value unknown
  Digit_Count : [1..5] init 3;
 
  // Attacker issues xor_in(2): XOR the PAN digit with 2
  // If the true digit is 0,1,2,...,7 -> error (2/10 chance); else pass (8/10)
  [] !P3_guessed & Digit_Count=3 &
     P3_could_be0 & P3_could_be1 & P3_could_be2 & P3_could_be3 &
     P3_could_be4 & P3_could_be5 & P3_could_be6 & P3_could_be7 &
     P3_could_be8 & P3_could_be9
  ->
  // error case: digits 0–7 produce a hex result, so 2 of 10 pass the check
  2/10 : (Digit_Count'=4) &
         (P3_could_be0'=false) & (P3_could_be1'=false) &
         (P3_could_be2'=false) & (P3_could_be3'=false) &
         (P3_could_be4'=false) & (P3_could_be5'=false) &
         (P3_could_be6'=false) & (P3_could_be7'=false)
  +
  // pass case: digits 8,9 survive; 8 of 10 give a decimal result
  8/10 : (Digit_Count'=3) &
         (P3_could_be8'=false) & (P3_could_be9'=false);
 
  // Attacker issues xor_in(8): XOR the PAN digit with 8
  [] !P3_guessed & Digit_Count=3 &
     P3_could_be0 & P3_could_be1 & P3_could_be2 & P3_could_be3 &
     P3_could_be4 & P3_could_be5 & P3_could_be6 & P3_could_be7 &
     P3_could_be8 & P3_could_be9
  ->
  6/10 : (Digit_Count'=3) &
         (P3_could_be0'=false) & (P3_could_be1'=false) &
         (P3_could_be8'=false) & (P3_could_be9'=false)
  +
  4/10 : (Digit_Count'=3) &
         (P3_could_be2'=false) & (P3_could_be3'=false) &
         (P3_could_be4'=false) & (P3_could_be5'=false) &
         (P3_could_be6'=false) & (P3_could_be7'=false);
 
  // Attacker issues xor_in(10): XOR the PAN digit with 10
  [] !P3_guessed & Digit_Count=3 &
     P3_could_be0 & P3_could_be1 & P3_could_be2 & P3_could_be3 &
     P3_could_be4 & P3_could_be5 & P3_could_be6 & P3_could_be7 &
     P3_could_be8 & P3_could_be9
  ->
  6/10 : (Digit_Count'=3) &
         (P3_could_be2'=false) & (P3_could_be3'=false) &
         (P3_could_be8'=false) & (P3_could_be9'=false)
  +
  4/10 : (Digit_Count'=3) &
         (P3_could_be0'=false) & (P3_could_be1'=false) &
         (P3_could_be4'=false) & (P3_could_be5'=false) &
         (P3_could_be6'=false) & (P3_could_be7'=false);
 
endmodule
 
rewards
  [] true : 1;
endrewards
```

There are a few features of this model that are worth noting:

**State encoding.** Rather than enumerating an explicit state for each possible PIN value, the mdoel uses a set of Boolean flags - one per candidate digit. The current knowledge state is fully captured by which flags remain `true`. This keeps the state space manageable while allowing the guard on each command to test the full set of remaining candidates. 

**Nondeterminism.** The three commands (`xor_in(2)`, `xor_in(8)`, `xor_in(10`) all have the same guard (all digits still possible, digit not yet guessed). PRISM treats these as nondeterministic choices. the MDP engine will determine which is optimal.

**Probabilistic outcomes.** Each command transitions to one of two successor states: an "error" branch (some candidates ruled out) and a "pass" branch (different candidates ruled out). The exact probabilities - 2/10, 8/10, 6/10, 4/10 - are dericed from how many of the ten equiprobable PIN digits would cause the HSM to report an arror for that particular XOR value.

**Rewards.** The `rewards` block charges 1 for every transition, so the expected reqard accumulated before reaching a goal state equals the expected number of HSM queries.

### 4.6 Properties and Analysis

The key quantitative property asked of this model is:
 
```
// Minimum expected number of queries to identify the PIN digit
Rmin=? [ F P3_guessed ]
```
 
PRISM minimizes over all nondeterministic choices (i.e., over all attacker strategies for sequencing the `xor_in` commands) and returns the expected number of steps under the optimal strategy. For a full model covering all four PIN digits, PRISM computes the complete optimal attack policy — not just the expected cost, but the exact sequence of commands to issue at each knowledge state.
 
The analysis confirmed that the reformatting attack can recover a 4-digit PIN in an expected number of queries far smaller than the 10,000 required by brute force. This illustrates the core value of the approach: PRISM does not merely confirm that an attack *exists*, but finds and quantifies the *best possible* attack automatically.
 
---

## 5. Further Topics
 
### 5.1 Rewards and Expected Costs
 
PRISM's reward framework lets modelers attach numerical values to states or transitions. Typical uses include:
 
- **Step counts**: reward 1 on each transition to compute expected time to reach a goal
- **Energy consumption**: reward the power consumed in each state to find minimum-energy strategies
- **Message overhead**: reward each transmitted message to minimize communication cost
Reward structures are declared separately from the model and can be stacked — a single model can carry multiple named reward structures analyzed independently.
 
```prism
rewards "energy"
  s=active : 2;   // 2 units per step while active
  s=idle   : 0.1; // 0.1 units per step while idle
endrewards
 
rewards "messages"
  [send] true : 1; // 1 message per send action
endrewards
```
 
### 5.2 Parametric Model Checking
 
PRISM supports **parametric** analysis, where transition probabilities are left as symbolic variables. Instead of a single numerical answer, PRISM computes a rational function expressing the result in terms of the parameters. This is useful when exact probability values are unknown or when the designer wants to find parameter ranges that guarantee a property.
 
### 5.3 PRISM-games
 
The companion tool **PRISM-games** extends PRISM to handle **stochastic multi-player games**, where two or more agents make nondeterministic choices adversarially or cooperatively. This enables analysis of multi-party security protocols, competitive systems, and scenarios with both an attacker and a defender whose strategies interact.
 
### 5.4 Limitations and Scalability
 
Like all exhaustive verification methods, PRISM faces the **state space explosion problem**: the number of states grows exponentially with the number of concurrent components. PRISM mitigates this with symbolic (BDD/MTBDD) and hybrid engine implementations, but practical models are typically bounded to tens of millions of states. For larger systems, statistical model checking tools (which sample execution paths rather than exploring the full state space) trade soundness for scalability.
 
---
 
## 6. History
 
Probabilistic model checking emerged in the early 1990s with the development of logics like PCTL (Hansson & Jonsson, 1994) and algorithms for verifying them against Markov chains. The PRISM tool began development around 1999 at the University of Birmingham under Marta Kwiatkowska and moved to Oxford, where it remains under active development as of 2024. PRISM is open-source software released under the GNU General Public License and runs on Linux, macOS, and Windows.
 
Key milestones include:
 
- **1999–2002**: Initial development; support for DTMCs and CTMCs with PCTL/CSL
- **~2004**: MDP support and reward-based properties added
- **~2007**: Symbolic and hybrid engines matured; tool gains widespread academic adoption
- **~2011**: PRISM-games fork begins, adding stochastic game support
- **2015–present**: Extensions to POMDPs, interval MDPs, and parametric model checking; continued maintenance
PRISM has been used in hundreds of published case studies spanning communication protocols (Bluetooth, Firewire), randomized distributed algorithms, biological systems (circadian clocks, gene regulatory networks), and security protocols (Crowds anonymity network, onion routing, PIN cracking).
 
---

## 7. PRISM Resources
- [PRISM Manual] (https://www.prismmodelchecker.org/manual/)
- [PRISM Case Studies] (https://www.prismmodelchecker.org/casestudies/index.php)
- [PRISM Benchmark Suites] (https://www.prismmodelchecker.org/benchmarks/)

## 8. References 

- Hansson, H., & Jonsson, B. (1994). A logic for reasoning about time and reliability. *Formal Aspects of Computing*, 6(5), 512–535. DOI: [10.1007/BF01211866](https://doi.org/10.1007/BF01211866). [PDF](https://web.stanford.edu/class/cs259/WWW08/papers/hansson94logic.pdf)
- Steel, G. (2006). Formal analysis of PIN block attacks. *Theoretical Computer Science*, 367(1–2), 257–270. DOI: [10.1016/j.tcs.2006.08.042](https://doi.org/10.1016/j.tcs.2006.08.042). [PDF](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/Steel-tcs06.pdf)
- Kwiatkowska, M., Norman, G., & Parker, D. (2007). Stochastic model checking. In M. Bernardo & J. Hillston (Eds.), *Formal Methods for Performance Evaluation* (SFM 2007), LNCS 4486, pp. 220–270. Springer. DOI: [10.1007/978-3-540-72522-0_6](https://doi.org/10.1007/978-3-540-72522-0_6). [PDF](https://www.researchgate.net/publication/221224404_Stochastic_Model_Checking) *(Recommended survey.)*
- Kwiatkowska, M., Norman, G., & Parker, D. (2011). PRISM 4.0: Verification of probabilistic real-time systems. In G. Gopalakrishnan & S. Qadeer (Eds.), *Computer Aided Verification* (CAV 2011), LNCS 6806, pp. 585–591. Springer. DOI: [10.1007/978-3-642-22110-1_47](https://doi.org/10.1007/978-3-642-22110-1_47)
- Kwiatkowska, M., Norman, G., Parker, D., & Santos, G. (2020). PRISM-games 3.0: Stochastic game verification with concurrency, equilibria and time. In S. Lahiri & C. Wang (Eds.), *Computer Aided Verification* (CAV 2020), LNCS 12225, pp. 475–487. Springer. DOI: [10.1007/978-3-030-53291-8_25](https://doi.org/10.1007/978-3-030-53291-8_25). [Tool page](https://www.prismmodelchecker.org/games/)
- Steel, G. (n.d.). PIN cracking schemes [PRISM case study]. University of Oxford. Retrieved from https://www.prismmodelchecker.org/casestudies/pincracking.php