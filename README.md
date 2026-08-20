# sdg-facelift

A public modernization of Riccardo Brasca and Gabriella Clemente's Lean 4 formalization of **Synthetic Differential Geometry (SDG)**.

## Goal

Port the mathematical core of [`riccardobrasca/SDG`](https://github.com/riccardobrasca/SDG) from its experimental reduced-choice toolchain to the current supported Lean/Mathlib release line, while preserving the constructive character of the development as far as the stable ecosystem permits.

The import baseline is upstream commit [`731ce9aba748554839a334dc7111651b039859a2`](https://github.com/riccardobrasca/SDG/commit/731ce9aba748554839a334dc7111651b039859a2) (2026-04-28).

## Upgrade target

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

Upstream currently uses a custom Lean toolchain and the `less_choice` Mathlib branch associated with Mathlib PR #35685. This repository deliberately targets ordinary stable Lean and Mathlib instead. The upstream `detectClassical` linter and unique-choice infrastructure are retained so that new dependencies on `Classical.choice` remain visible.

This means **"builds on stable" and "choice-free" are separate questions**. Stable Mathlib itself contains substantial classical dependencies; this repository does not claim otherwise.

## Status

Upgrade work is in progress. The first milestone is deliberately simple: import the upstream source nearly verbatim, switch only the toolchain/dependency configuration, and let CI expose the actual compatibility breakage. Fixes can then be made one incompatibility at a time.

## Attribution and license

The mathematical formalization being modernized here was written by **Riccardo Brasca** and **Gabriella Clemente** and is distributed under the Apache License 2.0. This repository is a derivative modernization effort; upstream remains the authoritative source for the original development.
