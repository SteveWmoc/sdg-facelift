module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public import SDG.Axiom.UniqueChoice
public import SDG.ForMathlib.FinChoiceFree

/-!
# Core definitions for Synthetic Differential Geometry

This file defines the subsemigroups `D R` and `𝔻 R k` of nilpotent elements, the Kock-Lawvere
axioms (`IsKockLawvere_one` and `IsKockLawvere`), and the synthetic derivative `deriv_fun`.
-/

@[expose] public section

open BigOperators

namespace SDG

variable (R : Type*) [CommRing R]

/-- The subsemigroup of nilpotent elements of order `k`: `{x : R | x^(k+1) = 0}`. -/
abbrev 𝔻 (k : ℕ) : Subsemigroup R where
 carrier := {(x : R) | x ^ (k + 1) = 0}
 mul_mem' := fun hx hy ↦ by simp_all [mul_pow]

/-- The first-order infinitesimals: `{x : R | x^2 = 0}`. -/
abbrev D := 𝔻 R 1

variable {R}

lemma D_mem_iff {x : R} : x ∈ D R ↔ x ^ 2 = 0 := Iff.rfl

lemma 𝔻_mem_iff {x : R} {k : ℕ} : x ∈ 𝔻 R k ↔ x ^ (k + 1) = 0 := Iff.rfl

variable (R) (k : ℕ)

lemma zero_mem_D : 0 ∈ D R := by
  simp

lemma zero_mem_𝔻 : 0 ∈ 𝔻 R k := by
  simp

instance : Zero (D R) where
  zero := ⟨0, zero_mem_D _⟩

instance : Zero (𝔻 R k) where
  zero := ⟨0, zero_mem_𝔻 _ _⟩

@[simp] lemma coe_zero (k : ℕ) : ((0 : 𝔻 R k) : R) = 0 := rfl

section IsKockLawvere

/-- The Kock-Lawvere axiom for first-order infinitesimals: every `g : D R → R` is uniquely
of the form `g d = g 0 + b * d` for some `b : R`. -/
class IsKockLawvere_one extends Nontrivial R where
  isKockLawvere_one : ∀ g : D R → R, ∃! b, ∀ d, g d = g 0 + b * d

/-- The general Kock-Lawvere axiom, stated using the choice-free finite sum. Every
`g : 𝔻 R k → R` is uniquely a polynomial of degree `k` in the infinitesimal. -/
class IsKockLawvere extends Nontrivial R where
  isKockLawvere_choiceFree : ∀ k, ∀ g : 𝔻 R k → R,
    ∃! b : Fin k → R, ∀ d,
      g d = g 0 + FinChoiceFree.sum k (fun i ↦ b i * d ^ (i.val + 1))

namespace IsKockLawvere

/-- Compatibility bridge from the choice-free Kock-Lawvere class field to Mathlib's generic
finite sum. This theorem intentionally inherits the axiom dependencies of the generic big operator. -/
theorem isKockLawvere [IsKockLawvere R] : ∀ k, ∀ g : 𝔻 R k → R,
    ∃! b : Fin k → R, ∀ d, g d = g 0 + ∑ i, b i * d ^ (i.val + 1) := by
  intro k g
  obtain ⟨b, hb, hbunique⟩ := IsKockLawvere.isKockLawvere_choiceFree k g
  refine ⟨b, ?_, ?_⟩
  · intro d
    rw [← FinChoiceFree.sum_eq_univ]
    exact hb d
  · intro b' hb'
    apply hbunique b'
    intro d
    rw [FinChoiceFree.sum_eq_univ]
    exact hb' d

end IsKockLawvere

instance [IsKockLawvere R] : IsKockLawvere_one R where
  isKockLawvere_one := fun g ↦ by
    obtain ⟨b, hb, hbunique⟩ := IsKockLawvere.isKockLawvere_choiceFree 1 g
    refine ⟨b 0, ?_, ?_⟩
    · intro d
      simpa only [FinChoiceFree.sum_succ, FinChoiceFree.sum_zero, add_zero, Fin.val_zero,
        zero_add, pow_one] using hb d
    · intro b' hb'
      have hfun := hbunique (fun _ ↦ b') (fun d ↦ by
        simpa only [FinChoiceFree.sum_succ, FinChoiceFree.sum_zero, add_zero, Fin.val_zero,
          zero_add, pow_one] using hb' d)
      exact congrFun hfun 0

variable [IsKockLawvere_one R]

open IsKockLawvere_one

variable {R}

/-- The synthetic derivative: the unique `b` such that `f (x + d) = f x + b * d`
for all `d : D R`. -/
noncomputable def deriv_fun (f : R → R) : R → R :=
  unique_choice_fun (fun x ↦ isKockLawvere_one (fun d ↦ f (x + d)))

end IsKockLawvere

end SDG