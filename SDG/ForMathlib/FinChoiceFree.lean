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

private theorem snoc_tail {α : Type*} {n : ℕ} (f : Fin (n + 1) → α) (x : α) :
    (fun i : Fin (n + 1) => Fin.snoc f x i.succ) =
      Fin.snoc (fun i : Fin n => f i.succ) x := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;> simp

@[simp]
theorem prod_snoc_one {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M), prod (n + 1) (Fin.snoc f 1) = prod n f
  | 0, f => by
      change Fin.snoc f 1 0 = 1
      simpa using Fin.snoc_last (1 : M) f
  | n + 1, f => by
      change Fin.snoc f 1 0 * prod (n + 1) (fun i => Fin.snoc f 1 i.succ) =
        f 0 * prod n (fun i => f i.succ)
      have h0 : Fin.snoc f 1 (0 : Fin (n + 2)) = f 0 := by
        simpa using Fin.snoc_castSucc (1 : M) f (0 : Fin (n + 1))
      rw [h0, snoc_tail f 1, prod_snoc_one]

@[simp]
theorem sum_snoc_zero {M : Type*} [AddMonoid M] :
    ∀ {n : ℕ} (f : Fin n → M), sum (n + 1) (Fin.snoc f 0) = sum n f
  | 0, f => by
      change Fin.snoc f 0 0 = 0
      simpa using Fin.snoc_last (0 : M) f
  | n + 1, f => by
      change Fin.snoc f 0 0 + sum (n + 1) (fun i => Fin.snoc f 0 i.succ) =
        f 0 + sum n (fun i => f i.succ)
      have h0 : Fin.snoc f 0 (0 : Fin (n + 2)) = f 0 := by
        simpa using Fin.snoc_castSucc (0 : M) f (0 : Fin (n + 1))
      rw [h0, snoc_tail f 0, sum_snoc_zero]

end FinChoiceFree
end SDG
