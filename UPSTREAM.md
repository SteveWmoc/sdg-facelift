# Upstream provenance

The initial mathematical source in this repository is derived from [`riccardobrasca/SDG`](https://github.com/riccardobrasca/SDG), the Synthetic Differential Geometry formalization by Riccardo Brasca and Gabriella Clemente.

## Import baseline

- Repository: `riccardobrasca/SDG`
- Commit: `731ce9aba748554839a334dc7111651b039859a2`
- Commit date: 2026-04-28
- License: Apache License 2.0

At the start of the facelift, `SDG.lean` and the files under `SDG/` were copied from that baseline without intentional mathematical changes. Git history records subsequent compatibility edits.

## What the facelift changes first

The original project uses the experimental reduced-choice ecosystem associated with Mathlib PR #35685:

- a custom Lean `less_choice` toolchain;
- Riccardo Brasca's `mathlib4:less_choice` branch;
- a matching reduced-choice Batteries dependency.

This repository instead targets the ordinary stable Lean/Mathlib release line. The first modernization pass changes the build environment and CI while retaining the upstream unique-choice axiom and `detectClassical` linter. Once the stable build is restored, those compatibility shims can be audited individually.

## Scope

This repository is initially a modernization of the Brasca–Clemente calculus library itself. Higher-level experiments involving microsquares, microcubes, strong difference, microlinearity, and Nishimura's general Jacobi identity should be layered on only after the stable port is healthy.
