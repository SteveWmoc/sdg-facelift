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
#print axioms SDG.IsKockLawvere.isKockLawvere_choiceFree
#print axioms SDG.IsKockLawvere.isKockLawvere
#print axioms SDG.instIsKockLawvere_oneOfIsKockLawvere
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

-- Generic arithmetic lemmas used by the scalar proofs but not covered above.
#print axioms Nat.factorial_ne_zero
#print axioms Nat.factorial_succ
#print axioms Nat.cast_succ
#print axioms Nat.cast_add
#print axioms Nat.cast_one

-- Concrete rational structure dictionaries and statement-only scalar probes.
#print axioms Rat.commRing
#print axioms Rat.commGroupWithZero
#print axioms Rat.instField
#print axioms Rat.instDivisionRing

-- Second-layer probes for the construction of `Rat.commRing`.
#print axioms Rat.addCommGroup
#print axioms Rat.commMonoid
#print axioms Rat.zero_add
#print axioms Rat.add_zero
#print axioms Rat.add_comm
#print axioms Rat.add_assoc
#print axioms Rat.neg_add_cancel
#print axioms Rat.sub_eq_add_neg
#print axioms Rat.zero_mul
#print axioms Rat.mul_zero
#print axioms Rat.mul_one
#print axioms Rat.one_mul
#print axioms Rat.mul_comm
#print axioms Rat.mul_assoc
#print axioms Rat.mul_add
#print axioms Rat.add_mul
#print axioms Rat.intCast_add
#print axioms Rat.intCast_one
#print axioms Rat.pow_zero
#print axioms Rat.pow_succ
#print axioms Rat.divInt_add_divInt
#print axioms Rat.intCast_eq_divInt
#print axioms Rat.divInt_one_one

-- Direct parent projections in the inverse hierarchy.
#print axioms DivInvMonoid.toInv
#print axioms DivisionRing.toDivInvMonoid
#print axioms Field.toDivisionRing

namespace SDG.Axiom

theorem ratInv_refl (q : ℚ) : q⁻¹ = q⁻¹ := rfl

theorem ratAlgebra_true {R : Type*} [CommRing R] [Algebra ℚ R] : True := True.intro

theorem ratInvSmul_refl {R : Type*} [CommRing R] [Algebra ℚ R] (q : ℚ) (x : R) :
    q⁻¹ • x = q⁻¹ • x := rfl

theorem ratInvMapMul_refl {R : Type*} [CommRing R] [Algebra ℚ R] (q : ℚ) (x : R) :
    algebraMap ℚ R q⁻¹ * x = algebraMap ℚ R q⁻¹ * x := rfl

-- Parametric controls: these distinguish proof-level contamination from dependencies already present
-- in generic field/algebra statements.
theorem genericField_true {K : Type*} [Field K] [CharZero K] : True := True.intro

theorem genericAlgebra_true {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] :
    True := True.intro

theorem genericInv_refl {K : Type*} [Field K] [CharZero K] (q : K) : q⁻¹ = q⁻¹ := rfl

theorem genericInvMapMul_refl
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] (q : K) (x : R) :
    algebraMap K R q⁻¹ * x = algebraMap K R q⁻¹ * x := rfl

theorem genericNatCastMapMul_refl
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] (n : ℕ) :
    algebraMap K R ((n : K)⁻¹) * (n : R) = algebraMap K R ((n : K)⁻¹) * (n : R) := rfl

-- Inverse hierarchy controls. `DivInvMonoid` contains `Inv` as data, so these probes determine
-- whether choice enters when typeclass inference forgets increasingly rich structures down to `Inv`.
theorem explicitInv_refl {K : Type*} [Inv K] (q : K) : q⁻¹ = q⁻¹ := rfl

theorem divInvMonoidInv_refl {K : Type*} [DivInvMonoid K] (q : K) : q⁻¹ = q⁻¹ := rfl

theorem divisionRingInv_refl {K : Type*} [DivisionRing K] (q : K) : q⁻¹ = q⁻¹ := rfl

theorem fieldExplicitInv_refl {K : Type*} [Field K] [Inv K] (q : K) : q⁻¹ = q⁻¹ := rfl

-- Force the direct parent projection instead of asking typeclass search to forget structure.
theorem divisionRingDirectDivInv_refl {K : Type*} [hK : DivisionRing K] (q : K) : q⁻¹ = q⁻¹ := by
  letI : DivInvMonoid K := hK.toDivInvMonoid
  rfl

theorem fieldDirectDivInv_refl {K : Type*} [hK : Field K] (q : K) : q⁻¹ = q⁻¹ := by
  letI : DivisionRing K := hK.toDivisionRing
  letI : DivInvMonoid K := (inferInstance : DivisionRing K).toDivInvMonoid
  rfl

-- Stronger bypass: name the inverse operation by explicit structure projections, so the theorem
-- statement itself never asks typeclass search for an `Inv K` instance.
def divisionRingChoiceFreeInv {K : Type*} [hK : DivisionRing K] : K → K :=
  hK.toDivInvMonoid.toInv.inv

def fieldChoiceFreeInv {K : Type*} [hK : Field K] : K → K :=
  hK.toDivisionRing.toDivInvMonoid.toInv.inv

theorem divisionRingChoiceFreeInv_refl {K : Type*} [DivisionRing K] (q : K) :
    divisionRingChoiceFreeInv q = divisionRingChoiceFreeInv q := rfl

theorem fieldChoiceFreeInv_refl {K : Type*} [Field K] (q : K) :
    fieldChoiceFreeInv q = fieldChoiceFreeInv q := rfl

theorem fieldChoiceFreeInvMapMul_refl
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] (q : K) (x : R) :
    algebraMap K R (fieldChoiceFreeInv q) * x =
      algebraMap K R (fieldChoiceFreeInv q) * x := rfl

theorem fieldChoiceFreeNatCastMapMul_refl
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R] (n : ℕ) :
    algebraMap K R (fieldChoiceFreeInv (n : K)) * (n : R) =
      algebraMap K R (fieldChoiceFreeInv (n : K)) * (n : R) := rfl

end SDG.Axiom

#print axioms SDG.Axiom.ratInv_refl
#print axioms SDG.Axiom.ratAlgebra_true
#print axioms SDG.Axiom.ratInvSmul_refl
#print axioms SDG.Axiom.ratInvMapMul_refl
#print axioms SDG.Axiom.genericField_true
#print axioms SDG.Axiom.genericAlgebra_true
#print axioms SDG.Axiom.genericInv_refl
#print axioms SDG.Axiom.genericInvMapMul_refl
#print axioms SDG.Axiom.genericNatCastMapMul_refl
#print axioms SDG.Axiom.explicitInv_refl
#print axioms SDG.Axiom.divInvMonoidInv_refl
#print axioms SDG.Axiom.divisionRingInv_refl
#print axioms SDG.Axiom.fieldExplicitInv_refl
#print axioms SDG.Axiom.divisionRingDirectDivInv_refl
#print axioms SDG.Axiom.fieldDirectDivInv_refl
#print axioms SDG.Axiom.divisionRingChoiceFreeInv
#print axioms SDG.Axiom.fieldChoiceFreeInv
#print axioms SDG.Axiom.divisionRingChoiceFreeInv_refl
#print axioms SDG.Axiom.fieldChoiceFreeInv_refl
#print axioms SDG.Axiom.fieldChoiceFreeInvMapMul_refl
#print axioms SDG.Axiom.fieldChoiceFreeNatCastMapMul_refl

#print axioms SDG.rat_natCast_ne_zero
#print axioms SDG.inv_factorial_algebraMap_mul_succ_iff
#print axioms SDG.inv_natCast_algebraMap_mul_natCast
#print axioms SDG.partial_deriv_propr
#print axioms SDG.partial_deriv_fun
#print axioms SDG.nat_fun_bounded_sum
