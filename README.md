# Generalized Fixed Point Characterizations of Expected Total Costs of MDPs in Lean

[![GitHub CI](https://github.com/expected-total-cost-of-mdps-in-lean/expected-total-cost-of-mdps-in-lean.github.io/actions/workflows/docs.yml/badge.svg)](https://github.com/expected-total-cost-of-mdps-in-lean/expected-total-cost-of-mdps-in-lean.github.io/actions/workflows/docs.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/expected-total-cost-of-mdps-in-lean/expected-total-cost-of-mdps-in-lean.github.io)

This repository holds Lean formalization of _Generalized Fixed Point Characterizations of Expected Total Costs of MDPs in Lean_.

The best way to explore the project is by visiting the [documentation](https://expected-total-cost-of-mdps-in-lean.github.io/MDP.html).

## Building the project

To build the project, one needs to install Lean. The recommended approach is to use VS Code as listed [here](https://lean-lang.org/lean4/doc/quickstart.html). If you prefer the CLI, install [elan](https://github.com/leanprover/elan?tab=readme-ov-file#installation) and run `lake build`.

## Formalizations efforts

- **_Markov Decision Processes_ (MDP)** [[Docs](https://expected-total-cost-of-mdps-in-lean.github.io/MDP.html)]
    - Formalization of countably infinite branching MDP.
    - Optimal expected cost of MDPs.
    - Fixed point formalization of expected cost and relation to finitely branching MDPs.
    - Connecting different interpretations of optimal expected cost across optimization order and history-dependence.
- **_probabilistic Guarded Command Language_ (pGCL)** [[Docs](https://expected-total-cost-of-mdps-in-lean.github.io/PGCL.html)]
    - Definition of a variant of pGCL and its operational semantics.
    - The induced MDP of the operational semantics of pGCL to define the expected costs of programs.
    - Connecting the _Weakest Preexpectation_ (WP) of pGCL programs to the optimal expected cost of the induced operational MDP by way of least fixed points.
