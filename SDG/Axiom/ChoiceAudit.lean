module

public import SDG.IsKockLawvere.TaylorMulti

/-!
# Classical-choice dependency audit

Temporary diagnostic module for tracing where `Classical.choice` enters the SDG dependency graph.
The `#print axioms` commands below deliberately print kernel axiom dependencies in CI logs.
-/

namespace SDG.Axiom

/-- A primitive-recursive product over `Fin n`, avoiding `Fintype`/`Finset` big-operator machinery. -/
def finProd {M : Type*} [Monoid M] : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 1
  | n + 1, f => f 0 * finProd n (fun i => f i.succ)

/-- Prepending `1` does not change the primitive-recursive finite product. -/
theorem finProd_cons_one {M : Type*} [Monoid M] {n : ℕ} (f : Fin n → M) :
    finProd (n + 1) (Fin.cons 1 f) = finProd n f := by
  simp [finProd]

end SDG.Axiom

#print axioms SDG.Axiom.finProd
#print axioms SDG.Axiom.finProd_cons_one

#print axioms Fin.prod_univ_succAbove
#print axioms Fin.prod_univ_succ
#print axioms Fin.prod_univ_castSucc
#print axioms Fin.prod_cons
#print axioms Fin.prod_snoc
#print axioms Fin.prod_univ_add
#print axioms Fintype.prod_equiv

#print axioms Fin.prod_ofFn
#print axioms Fin.prod_univ_def
#print axioms Fin.prod_univ_zero
#print axioms Finset.prod_eq_one

#print axioms Fin.prod_cons_one
#print axioms Fin.sum_cons_zero
#print axioms Fin.prod_castLE_of_eq_one
#print axioms Fin.sum_castLE_of_eq_zero

#print axioms SDG.IsKockLawvere
#print axioms SDG.cancel_d
#print axioms SDG.cancel_d_fun
#print axioms SDG.mem_D_sum_pow_succ
#print axioms SDG.mem_D_sum_pow

#print axioms SDG.inv_factorial_smul_succ_iff
#print axioms SDG.inv_natCast_smul_natCast
#print axioms SDG.partial_deriv_propr
#print axioms SDG.partial_deriv_fun
#print axioms SDG.nat_fun_bounded_sum
