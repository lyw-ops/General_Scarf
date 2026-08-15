# General Scarf in Lean

This repository contains a Lean formalization of the main dependency structure and applications
in Nikolai Ivanov's [*Scarf's theorems, simplices, and oriented
matroids*](https://arxiv.org/abs/2207.10832).

The repository contains only the `BeyondSperner` development. The separate `Gametheory`
formalization of Brouwer's fixed-point theorem and Nash equilibria is not included here.

## Formalization blueprint

The arrows show how one formalized layer supplies the next theorem or application.

```mermaid
flowchart TD
    SC["Finite simplicial complexes<br/>simplex families and F₂ chains"]
    PS["Pseudo-simplex incidence"]
    CS["Chain-simplex boundary identity"]
    OR["Indexed linear orders<br/>dominant sets and associated families"]

    OM["Signed-circuit oriented matroids<br/>weak elimination only"]
    WS["Finite weak-to-strong elimination"]
    DU["Underlying matroid, cocircuits,<br/>Farkas, duality, Todd"]
    LX["Constructed lexicographic<br/>one-point extension"]

    ND["Nondegenerate coloring<br/>Theorem 6.5 and odd parity"]
    PT["Perturbation setup<br/>Lemmas 8.1–8.4"]
    GS["Theorem 8.5<br/>generalized Scarf"]

    VS["Realizable/vector Scarf<br/>Section 7"]
    CL["Classical colorful-cell Scarf"]
    BR["Scarf → Brouwer<br/>standard and affine simplices"]
    KA["Vector Scarf → Kakutani<br/>closed-graph limit"]

    CH["Section 10 chains and<br/>intersection numbers"]
    T8A["Theorem 10.8<br/>paper intersection route"]
    T8B["Theorem 10.8<br/>oriented-matroid route"]
    T910["Theorems 10.9 and 10.10"]

    FR["Freudenthal/Scarf complexes<br/>Section 4"]
    GT["Finite geometric triangulations<br/>minimal data → purity/nonbranching"]

    SC --> PS --> CS
    OR --> PS
    OM --> WS --> DU --> LX
    DU --> ND
    LX --> PT
    ND --> PT --> GS
    CS --> GS
    OR --> GS

    GS --> VS --> KA
    GS --> CL --> BR

    CS --> CH --> T8A --> T910
    DU --> T8B --> T910
    FR --> CS
    FR --> T910
    GT --> CS
    GT --> T910
```

The two Theorem 10.8 nodes are dependency-independent: one follows the paper's intersection-number
route, while the other is supplied by the oriented-matroid coloring route. Both feed the common
Theorem 10.9 and Theorem 10.10 application layers.

## Build

The project uses Lean `4.33.0` and mathlib `v4.33.0`, pinned by `lean-toolchain` and
`lake-manifest.json`.

```bash
lake build
```

The formalization and representative axiom closures can also be checked with:

```bash
lake env lean FormalizationInterface/AuditAll.lean
lake env lean FormalizationInterface/Audit.lean
```

## Repository layout

- [`BeyondSperner.lean`](BeyondSperner.lean) is the umbrella import.
- [`BeyondSperner/`](BeyondSperner/) contains the mathematical formalization.
- [`FormalizationInterface/`](FormalizationInterface/) contains theorem-route adapters, status
  documentation, and executable audits.

For a detailed correspondence between the paper and Lean declarations, see
[`FormalizationInterface/BeyondSperner.md`](FormalizationInterface/BeyondSperner.md). For the
formalization status and proof architecture, see
[`FormalizationInterface/STATUS.md`](FormalizationInterface/STATUS.md).
