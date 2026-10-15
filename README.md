# Modeling the ABP Work-Stealing Deque Under SC and TSO Using TLA+

This project explores how memory-model assumptions affect the modeling and verification of the Arora–Blumofe–Plaxton (ABP) work-stealing deque using TLA+ and the TLC model checker.

Developed as a course project for **CPSC 521 at the University of British Columbia (Fall 2025)**, it compares an idealized sequential consistency (SC) model with a simplified Total Store Order (TSO) model to examine the effects of memory visibility, ordering, and atomicity on concurrent execution.

## Approach

Two TLA+ specifications were developed:

- **SC model:** Provides a simplified reference model in which shared-state updates are atomic and immediately visible to all threads.
- **TSO model:** Introduces buffered writes to the bottom index and simplified compare-and-swap (CAS) semantics to explore behaviors under relaxed memory assumptions.

Both models were explored using TLC to check safety invariants and examine execution traces.

## Results and Limitations

TLC verified the specified invariants across the tested SC configurations, including variations in queue size and the number of thief threads.

In the simplified TSO model, TLC generated counterexamples involving duplicate task removals. Analysis of these traces revealed limitations in the model's representation of CAS atomicity, memory ordering, and shared-state consistency.

**These counterexamples do not establish a correctness flaw in the ABP algorithm or its real-world implementations.** The simplified synchronization semantics may admit executions that would not be possible under a more faithful hardware model.

The project therefore illustrates both the usefulness of TLA+ for exploring weak-memory behaviors and the importance of accurately modeling synchronization semantics.

## Repository Contents

| File | Description |
|---|---|
| `sc.tla` | TLA+ specification of the SC model |
| `sc.cfg` | TLC configuration for the SC model |
| `tso.tla` | TLA+ specification of the simplified TSO model |
| `tso.cfg` | TLC configuration for the TSO model |
