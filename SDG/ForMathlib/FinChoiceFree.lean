module

public import Mathlib.Data.Fin.Basic

/-!
# Choice-free finite folds over `Fin`

Primitive-recursive finite sums and products over `Fin n`, designed to avoid the generic
`Fintype`/`Finset` big-operator infrastructure and its `Classical.choice` dependency.
-/

@[expose] public section

namespace SDG
namespace FinChoiceFree

/-- Primitive-recursive product over `Fin n`. -/
def prod {M : Type*} [Monoid M] : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 1
  | n + 1, f => f 0 * prod n (fun i => f i.succ)

/-- Primitive-recursive sum over `Fin n`. -/
def sum {M : Type*} [AddMonoid M] : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 0
  | n + 1, f => f 0 + sum n (fun i => f i.succ)

@[simp]
theorem prod_zero {M : Type*} [Monoid M] (f : Fin 0 → M) : prod 0 f = 1 := rfl

@[simp]
theorem sum_zero {M : Type*} [AddMonoid M] (f : Fin 0 → M) : sum 0 f = 0 := rfl

@[simp]
theorem prod_succ {M : Type*} [Monoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    prod (n + 1) f = f 0 * prod n (fun i => f i.succ) := rfl

@[simp]
theorem sum_succ {M : Type*} [AddMonoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    sum (n + 1) f = f 0 + sum n (fun i => f i.succ) := rfl

@[simp]
theorem prod_cons_one {M : Type*} [Monoid M] {n : ℕ} (f : Fin n → M) :
    prod (n + 1) (Fin.cons 1 f) = prod n f := by
  simp [prod]

@[simp]
theorem sum_cons_zero {M : Type*} [AddMonoid M] {n : ℕ} (f : Fin n → M) :
    sum (n + 1) (Fin.cons 0 f) = sum n f := by
  simp [sum]

@[simp]
theorem prod_snoc_one {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M), prod (n + 1) (Fin.snoc f 1) = prod n f
  | 0, f => by
      simp [prod]
  | n + 1, f => by
      simp [prod, prod_snoc_one (fun i => f i.succ)]

@[simp]
theorem sum_snoc_zero {M : Type*} [AddMonoid M] :
    ∀ {n : ℕ} (f : Fin n → M), sum (n + 1) (Fin.snoc f 0) = sum n f
  | 0, f => by
      simp [sum]
  | n + 1, f => by
      simp [sum, sum_snoc_zero (fun i => f i.succ)]

end FinChoiceFree
end SDG
