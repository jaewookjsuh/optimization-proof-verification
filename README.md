# inequality-proof-verification

This is a personal scratch project to build a **symbolic inner-product engine from scratch**
and use it to verify inequalities in optimization.

## Goals

- Implement a minimal symbolic engine for inner products, scalars, vectors, and their operations
- Verify convergence proofs for optimization algorithms

## Scope

- Verifies equalities in inner product spaces.
- Verifies simple proof structures such as Lyapunov proofs.
- This repository is not intended as a production-ready package.
- API stability and backward compatibility are not priorities.

## Current Structure

- `verify_objects.py`: symbolic objects (scalar/vector/operations)
- `verify_relation.py`: relation and inference logic
- `verifier.py`: verification utilities
- `example*.ipynb`: notebook experiments for one-step proofs

## How It Is Used

Open the notebooks and run the examples to check whether assumed facts and target goals 
are consistently validated by the engine logic.

---

This repository captures past experiments and is kept as a scratch project, not an actively maintained codebase.

Note:
- Last substantive update was in 2023.
- In 2026, only light cleanup work was done.
- Most tactic-related implementation in `verifier.py` was done by Hyunsik Chae.

