module

public import SDG.ForMathlib.FinChoiceFree
public import SDG.IsKockLawvere.TaylorMulti

/-!
# Classical-choice dependency audit

Temporary diagnostic module for tracing where `Classical.choice` enters the SDG dependency graph.
The `#print axioms` commands below deliberately print kernel axiom dependencies in CI logs.
-/

#print axioms SDG.FinChoiceFree.prod
#print axioms SDG.FinChoiceFree.sum
#print axioms SDG.FinChoiceFree.prod_cons_one
#print axioms SDG.FinChoiceFree.sum_cons_zero
#print axioms SDG.FinChoiceFree.prod_snoc
#print axioms SDG.FinChoiceFree.sum_snoc
#print axioms SDG.FinChoiceFree.prod_snoc_apply
#print axioms SDG.FinChoiceFree.sum_snoc_apply
#print axioms SDG.FinChoiceFree.prod_snoc_one
#print axioms SDG.FinChoiceFree.sum_snoc_zero
#print axioms SDG.FinChoiceFree.prod_castLE_of_eq_one
#print axioms SDG.FinChoiceFree.sum_castLE_of_eq_zero
#print axioms SDG.FinChoiceFree.prod_eq_univ
#print axioms SDG.FinChoiceFree.sum_eq_univ

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
