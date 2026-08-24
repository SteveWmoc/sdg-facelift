module

public import Mathlib.Algebra.BigOperators.Fin

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

/-- Nondependent primitive-recursive `snoc` for `Fin`-indexed tuples. -/
def snoc {α : Type*} : (n : ℕ) → (Fin n → α) → α → Fin (n + 1) → α
  | 0, _, x => fun _ => x
  | n + 1, f, x => Fin.cons (f 0) (snoc n (fun i => f i.succ) x)

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
    ∀ (n : ℕ) (f : Fin n → M), prod (n + 1) (snoc n f 1) = prod n f
  | 0, f => by
      simp [prod, snoc]
  | n + 1, f => by
      change f 0 * prod (n + 1) (snoc n (fun i => f i.succ) 1) =
        f 0 * prod n (fun i => f i.succ)
      rw [prod_snoc_one n (fun i => f i.succ)]

@[simp]
theorem sum_snoc_zero {M : Type*} [AddMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M), sum (n + 1) (snoc n f 0) = sum n f
  | 0, f => by
      simp [sum, snoc]
  | n + 1, f => by
      change f 0 + sum (n + 1) (snoc n (fun i => f i.succ) 0) =
        f 0 + sum n (fun i => f i.succ)
      rw [sum_snoc_zero n (fun i => f i.succ)]

end FinChoiceFree
end SDG
