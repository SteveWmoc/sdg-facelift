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
#print axioms SDG.mem_D_univ_sum_pow_succ
#print axioms SDG.mem_D_univ_sum_pow

-- Rational-scalar dependency roots.
#print axioms Algebra.smul_def
#print axioms map_natCast
#print axioms map_mul
#print axioms map_one
#print axioms Nat.cast_ne_zero
#print axioms Nat.cast_mul
#print axioms Rat.natCast_injective
#print axioms Rat.num_natCast
#print axioms Rat.num_zero
#print axioms Int.ofNat.inj
#print axioms mul_inv_cancel₀
#print axioms inv_mul_cancel₀
#print axioms mul_inv_rev
#print axioms smul_smul
#print axioms one_smul

-- Concrete rational structure dictionaries and statement-only scalar probes.
#print axioms Rat.commRing
#print axioms Rat.commGroupWithZero
#print axioms Rat.instField
#print axioms Rat.instDivisionRing

namespace SDG.Axiom

theorem ratInv_refl (q : ℚ) : q⁻¹ = q⁻¹ := rfl

theorem ratAlgebra_true {R : Type*} [CommRing R] [Algebra ℚ R] : True := True.intro

theorem ratInvSmul_refl {R : Type*} [CommRing R] [Algebra ℚ R] (q : ℚ) (x : R) :
    q⁻¹ • x = q⁻¹ • x := rfl

theorem ratInvMapMul_refl {R : Type*} [CommRing R] [Algebra ℚ R] (q : ℚ) (x : R) :
    algebraMap ℚ R q⁻¹ * x = algebraMap ℚ R q⁻¹ * x := rfl

end SDG.Axiom

#print axioms SDG.Axiom.ratInv_refl
#print axioms SDG.Axiom.ratAlgebra_true
#print axioms SDG.Axiom.ratInvSmul_refl
#print axioms SDG.Axiom.ratInvMapMul_refl

#print axioms SDG.rat_natCast_ne_zero
#print axioms SDG.inv_factorial_algebraMap_mul_succ_iff
#print axioms SDG.inv_natCast_algebraMap_mul_natCast
#print axioms SDG.partial_deriv_propr
#print axioms SDG.partial_deriv_fun
#print axioms SDG.nat_fun_bounded_sum
