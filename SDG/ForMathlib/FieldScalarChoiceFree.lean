module

public import SDG.ForMathlib.FieldChoiceFree
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Choice-free scalar identities over fields

Algebraic convenience lemmas built on `FieldChoiceFree.inv`. These avoid the standard
`Field K → Inv K` forgetful instance path, while retaining Mathlib's field and algebra structures.
-/

@[expose] public section

namespace SDG
namespace FieldChoiceFree

open Nat

/-- The factorial-scalar step, expressed using the explicitly projected field inverse. -/
theorem inv_factorial_algebraMap_mul_succ_iff {K R : Type*} [Field K] [CharZero K]
    [CommRing R] [Algebra K R] {n : ℕ} {x y : R} :
    algebraMap K R (inv (n ! : K)) * y = algebraMap K R (inv ((n + 1)! : K)) * x ↔
      x = (n + 1) * y := by
  have hfact : (n ! : K) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero n)
  have hsuccfact : ((n + 1)! : K) ≠ 0 := Nat.cast_ne_zero.mpr (factorial_ne_zero (n + 1))
  have hfac : ((n + 1)! : K) = (↑(n + 1) : K) * (n ! : K) := by
    rw [factorial_succ, Nat.cast_mul]
  have hstep : algebraMap K R (↑(n + 1) : K) = (↑(n + 1) : R) := by
    rw [map_natCast]
  constructor
  · intro h
    have h' := congrArg (fun z : R ↦ algebraMap K R ((n + 1)! : K) * z) h
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul] at h'
    have hleft : ((n + 1)! : K) * inv (n ! : K) = (↑(n + 1) : K) := by
      rw [hfac, mul_assoc, mul_inv_cancel hfact, mul_one]
    have hright : ((n + 1)! : K) * inv ((n + 1)! : K) = 1 :=
      mul_inv_cancel hsuccfact
    rw [hleft, hright, map_one, one_mul] at h'
    calc
      x = algebraMap K R (↑(n + 1) : K) * y := h'.symm
      _ = (↑(n + 1) : R) * y := by rw [hstep]
      _ = (n + 1) * y := by rw [Nat.cast_succ]
  · intro h
    have hxR : x = (↑(n + 1) : R) * y := by
      simpa only [Nat.cast_succ] using h
    have hscalar : inv ((n + 1)! : K) * (↑(n + 1) : K) = inv (n ! : K) := by
      apply mul_right_cancel hfact
      rw [← mul_assoc, ← hfac, inv_mul_cancel hsuccfact, inv_mul_cancel hfact]
    rw [hxR, ← hstep, ← mul_assoc, ← map_mul, hscalar]

/-- Cancellation of an inverse natural-number scalar after applying an algebra map. -/
theorem inv_natCast_algebraMap_mul_natCast {K R : Type*} [Field K] [CharZero K]
    [CommRing R] [Algebra K R] {n : ℕ} (hn : n ≠ 0) :
    algebraMap K R (inv (n : K)) * (n : R) = 1 := by
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← map_natCast (algebraMap K R), ← map_mul, inv_mul_cancel hnK, map_one]

end FieldChoiceFree
end SDG
