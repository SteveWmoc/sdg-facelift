module

public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Fin

public import SDG.Basic.Defs
public import SDG.ForMathlib.FinChoiceFree

/-!
# Lemmas about nilpotent subsemigroups

Algebraic properties of `D R` and `𝔻 R k`: closure under multiplication, powers, sums of
nilpotents, and related combinatorial identities involving factorials.
-/

@[expose] public section

namespace SDG

open Function BigOperators Nat

variable {R : Type*} [CommRing R] {k : ℕ}

lemma 𝔻_mul_mem {x : R} (y : R) (hx : x ∈ 𝔻 R k) : y * x ∈ 𝔻 R k := by
  simp [mul_pow, 𝔻_mem_iff.1 hx]

lemma 𝔻_mem_mul {x : R} (y : R) (hx : x ∈ 𝔻 R k) : x * y ∈ 𝔻 R k := by
  simp [mul_pow, 𝔻_mem_iff.1 hx]

@[simp] lemma 𝔻_pow (x : 𝔻 R k) : (x : R) ^ (k + 1) = 0 :=
  x.2

lemma 𝔻_le {k ℓ : ℕ} (h : k ≤ ℓ) : (𝔻 R k) ≤ 𝔻 R ℓ := by
  refine fun x hx ↦ 𝔻_mem_iff.2 ?_
  calc
    x ^ (ℓ + 1) = x ^ (k + 1 + (ℓ - k)) := by congr 1; zify [h]; ring
              _ = x ^ (k + 1) * x ^ (ℓ - k) := by ring
              _ = 0 := by simp [𝔻_mem_iff.1 hx]

lemma D_add_sq (d₁ d₂ : D R) : (d₁ + d₂ : R) ^ 2 = 2 * d₁ * d₂ :=
  calc (d₁ + d₂ : R) ^ 2 = d₁ ^ 2 + d₂ ^ 2 + 2 * d₁ * d₂ := by ring
                       _ = _ := by simp

lemma mem_𝔻_of_mem_D_add_mem_D (d₁ d₂ : D R) : (d₁ + d₂ : R) ∈ 𝔻 R 2 :=
  calc
    (d₁ + d₂ : R) ^ 3 = d₁ ^ 2 * (d₁ + 3 * d₂) + d₂ ^ 2 * (3 * d₁ + d₂) := by ring
                    _ = 0 := by simp

open Multiset Finset

theorem mem_D_add_pow (x : D R) (y : R) : ∀ (k : ℕ), (x + y) ^ (k + 1) =
  (↑(k + 1) : R) * x * y ^ k + y ^ (k + 1)
| 0 => by simp
| k + 1 => by
  rw [pow_succ, mem_D_add_pow x]
  simp only [cast_add, cast_one]
  calc _ = y ^ (k + 2) + y ^ (k + 1) * x + (k + 1) * x * y ^ (k + 1) +
    (k + 1) * x ^ 2 * y ^ k := by ring
       _ = _ := by simp; ring

/-- Choice-free finite-sum form of `mem_D_sum_pow_succ`. -/
lemma mem_D_sum_pow_succ_choiceFree : ∀ {k : ℕ} (b : Fin k → D R),
    (FinChoiceFree.sum k (fun i => (b i : R))) ^ (k + 1) = 0
| 0 => fun _ ↦ by
  rw [zero_add, pow_one]
  rfl
| k + 1 => fun b ↦ by
  rw [FinChoiceFree.sum_succ, mem_D_add_pow, mem_D_sum_pow_succ_choiceFree, mul_zero,
    zero_add, pow_succ, mem_D_sum_pow_succ_choiceFree, zero_mul]

/-- Choice-free finite-sum/product form of `mem_D_sum_pow`. -/
lemma mem_D_sum_pow_choiceFree : ∀ {k : ℕ} (b : Fin k → D R),
    (FinChoiceFree.sum k (fun i => (b i : R))) ^ k =
      (k ! : R) * FinChoiceFree.prod k (fun i => (b i).1)
| 0 => fun _ ↦ by
  simp only [FinChoiceFree.sum_zero, FinChoiceFree.prod_zero, pow_zero, factorial_zero,
    cast_one, one_mul]
| k + 1 => fun b ↦ by
  rw [FinChoiceFree.sum_succ, mem_D_add_pow, mem_D_sum_pow_succ_choiceFree, add_zero,
    mem_D_sum_pow_choiceFree, FinChoiceFree.prod_succ, factorial_succ, cast_mul]
  ring

/-- Compatibility form using Mathlib's generic finite sum. -/
lemma mem_D_sum_pow_succ {k : ℕ} (b : Fin k → D R) :
    (∑ i, (b i : R)) ^ (k + 1) = 0 := by
  rw [← FinChoiceFree.sum_eq_univ]
  exact mem_D_sum_pow_succ_choiceFree b

/-- Compatibility form using Mathlib's generic finite sum and product. -/
lemma mem_D_sum_pow {k : ℕ} (b : Fin k → D R) :
    (∑ i, (b i : R)) ^ k = (k ! : R) * ∏ i, (b i).1 := by
  rw [← FinChoiceFree.sum_eq_univ, ← FinChoiceFree.prod_eq_univ]
  exact mem_D_sum_pow_choiceFree b

lemma D_add_sq_dvd_two [Invertible (2 : R)] (d₁ d₂ : D R) :
    (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ := by
  calc (d₁ + d₂ : R) ^ 2 * ⅟2 = d₁ * d₂ * 2 * ⅟2 := by rw [D_add_sq]; ring
    _ = d₁ * d₂ := by simp [mul_assoc]

variable (R) in
lemma coe_sq : ((↑) : D R → R) * (↑) = 0 := by
  ext d
  simpa only [Pi.mul_apply, Pi.zero_apply, pow_two] using D_mem_iff.1 d.2

variable (R) (k : ℕ) in
lemma coe_pow : ((↑) : 𝔻 R k → R) ^ (k + 1) = 0 := by
  ext d
  simp

end SDG
