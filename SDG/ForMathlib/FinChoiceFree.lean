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
theorem prod_snoc {M : Type*} [Monoid M] :
    ∀ (n : ℕ) (f : Fin n → M) (x : M), prod (n + 1) (snoc n f x) = prod n f * x
  | 0, f, x => by
      simp [prod, snoc]
  | n + 1, f, x => by
      change f 0 * prod (n + 1) (snoc n (fun i => f i.succ) x) =
        (f 0 * prod n (fun i => f i.succ)) * x
      rw [prod_snoc n (fun i => f i.succ) x]
      exact (mul_assoc ..).symm

@[simp]
theorem sum_snoc {M : Type*} [AddMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M) (x : M), sum (n + 1) (snoc n f x) = sum n f + x
  | 0, f, x => by
      simp [sum, snoc]
  | n + 1, f, x => by
      change f 0 + sum (n + 1) (snoc n (fun i => f i.succ) x) =
        (f 0 + sum n (fun i => f i.succ)) + x
      rw [sum_snoc n (fun i => f i.succ) x]
      exact (add_assoc ..).symm

@[simp]
theorem prod_snoc_apply {α M : Type*} [Monoid M] (g : α → M) :
    ∀ (n : ℕ) (f : Fin n → α) (x : α),
      prod (n + 1) (fun i => g (snoc n f x i)) = prod n (fun i => g (f i)) * g x
  | 0, f, x => by
      simp [prod, snoc]
  | n + 1, f, x => by
      change g (f 0) * prod (n + 1) (fun i => g (snoc n (fun j => f j.succ) x i)) =
        (g (f 0) * prod n (fun i => g (f i.succ))) * g x
      rw [prod_snoc_apply g n (fun i => f i.succ) x]
      exact (mul_assoc ..).symm

@[simp]
theorem sum_snoc_apply {α M : Type*} [AddMonoid M] (g : α → M) :
    ∀ (n : ℕ) (f : Fin n → α) (x : α),
      sum (n + 1) (fun i => g (snoc n f x i)) = sum n (fun i => g (f i)) + g x
  | 0, f, x => by
      simp [sum, snoc]
  | n + 1, f, x => by
      change g (f 0) + sum (n + 1) (fun i => g (snoc n (fun j => f j.succ) x i)) =
        (g (f 0) + sum n (fun i => g (f i.succ))) + g x
      rw [sum_snoc_apply g n (fun i => f i.succ) x]
      exact (add_assoc ..).symm

@[simp]
theorem prod_snoc_one {M : Type*} [Monoid M] (n : ℕ) (f : Fin n → M) :
    prod (n + 1) (snoc n f 1) = prod n f := by
  simpa using prod_snoc n f 1

@[simp]
theorem sum_snoc_zero {M : Type*} [AddMonoid M] (n : ℕ) (f : Fin n → M) :
    sum (n + 1) (snoc n f 0) = sum n f := by
  simpa using sum_snoc n f 0

lemma prod_eq_one {M : Type*} [Monoid M] :
    ∀ (n : ℕ) (f : Fin n → M), (∀ i, f i = 1) → prod n f = 1
  | 0, f, hf => rfl
  | n + 1, f, hf => by
      rw [prod_succ, hf 0, one_mul]
      exact prod_eq_one n (fun i => f i.succ) (fun i => hf i.succ)

lemma sum_eq_zero {M : Type*} [AddMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M), (∀ i, f i = 0) → sum n f = 0
  | 0, f, hf => rfl
  | n + 1, f, hf => by
      rw [sum_succ, hf 0, zero_add]
      exact sum_eq_zero n (fun i => f i.succ) (fun i => hf i.succ)

lemma prod_castLE_of_eq_one {M : Type*} [Monoid M] {a b : ℕ} (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ i, a ≤ i.1 → f i = 1) : prod b f = prod a (fun i => f (Fin.castLE h i)) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero h
      subst a
      rfl
  | succ b ih =>
      cases a with
      | zero =>
          rw [prod_zero]
          exact prod_eq_one (b + 1) f (fun i => hf i (Nat.zero_le _))
      | succ a =>
          have h' : a ≤ b := Nat.succ_le_succ_iff.mp h
          change f 0 * prod b (fun i => f i.succ) =
            f 0 * prod a (fun i => f (Fin.castLE h' i).succ)
          congr 1
          exact ih h' (fun i => f i.succ)
            (fun i hi => hf i.succ (Nat.succ_le_succ hi))

lemma sum_castLE_of_eq_zero {M : Type*} [AddMonoid M] {a b : ℕ} (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ i, a ≤ i.1 → f i = 0) : sum b f = sum a (fun i => f (Fin.castLE h i)) := by
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero h
      subst a
      rfl
  | succ b ih =>
      cases a with
      | zero =>
          rw [sum_zero]
          exact sum_eq_zero (b + 1) f (fun i => hf i (Nat.zero_le _))
      | succ a =>
          have h' : a ≤ b := Nat.succ_le_succ_iff.mp h
          change f 0 + sum b (fun i => f i.succ) =
            f 0 + sum a (fun i => f (Fin.castLE h' i).succ)
          congr 1
          exact ih h' (fun i => f i.succ)
            (fun i hi => hf i.succ (Nat.succ_le_succ hi))

/-- Bridge to Mathlib's generic big-operator product. This bridge itself inherits the generic
big-operator axiom dependencies and is intended only for incremental migration of existing proofs. -/
lemma prod_eq_univ {M : Type*} [CommMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M), prod n f = ∏ i, f i
  | 0, f => by simp [prod]
  | n + 1, f => by
      rw [prod_succ, Fin.prod_univ_succ, prod_eq_univ]

/-- Additive bridge to Mathlib's generic big-operator sum. -/
lemma sum_eq_univ {M : Type*} [AddCommMonoid M] :
    ∀ (n : ℕ) (f : Fin n → M), sum n f = ∑ i, f i
  | 0, f => by simp [sum]
  | n + 1, f => by
      rw [sum_succ, Fin.sum_univ_succ, sum_eq_univ]

end FinChoiceFree
end SDG
