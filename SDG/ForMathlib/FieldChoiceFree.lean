module

public import Mathlib.Algebra.Field.Defs

/-!
# Choice-free access to field inverse data

The standard forgetful typeclass path from `Field K` to `Inv K` currently carries a
`Classical.choice` dependency. The inverse operation itself is already data stored in the field
structure, so this module exposes it by explicit structure projection instead of asking typeclass
inference to recover `Inv K`.

This is intended as a small compatibility layer for choice-free developments that otherwise use
Mathlib's algebraic hierarchy normally.
-/

@[expose] public section

namespace SDG
namespace FieldChoiceFree

/-- The inverse operation carried by a `DivisionRing`, reached only by structure projection. -/
def divisionRingInv {K : Type*} [hK : DivisionRing K] : K → K :=
  hK.toDivInvMonoid.toInv.inv

/-- The inverse operation carried by a `Field`, reached only by structure projection. -/
def inv {K : Type*} [hK : Field K] : K → K :=
  hK.toDivisionRing.toDivInvMonoid.toInv.inv

/-- Right inverse cancellation for the explicitly projected field inverse. -/
theorem mul_inv_cancel {K : Type*} [hK : Field K] {a : K} (ha : a ≠ 0) :
    a * inv a = 1 := by
  change a * hK.toDivisionRing.toDivInvMonoid.toInv.inv a = 1
  exact hK.toDivisionRing.mul_inv_cancel a ha

/-- Left inverse cancellation for the explicitly projected field inverse. -/
theorem inv_mul_cancel {K : Type*} [hK : Field K] {a : K} (ha : a ≠ 0) :
    inv a * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel ha

/-- Cancel a nonzero right factor without inferring a `GroupWithZero` or cancellation instance. -/
theorem mul_right_cancel {K : Type*} [Field K] {a b c : K} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have h' := congrArg (fun z : K ↦ z * inv c) h
  simpa only [mul_assoc, mul_inv_cancel hc, mul_one] using h'

/-- Cancel a nonzero left factor without inferring a `GroupWithZero` or cancellation instance. -/
theorem mul_left_cancel {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0)
    (h : a * b = a * c) : b = c := by
  rw [mul_comm a b, mul_comm a c] at h
  exact mul_right_cancel ha h

end FieldChoiceFree
end SDG
