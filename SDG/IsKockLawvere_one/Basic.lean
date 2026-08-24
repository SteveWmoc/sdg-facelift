module

public import SDG.Basic.Defs
public import SDG.ForMathlib.FinChoiceFree

/-!
# Basic consequences of the first-order Kock-Lawvere axiom

Infinitesimal cancellation (`cancel_d`, `cancel_d_fun`) and nontriviality of `D R`.
-/

@[expose] public section

namespace SDG

variable {R : Type*} [CommRing R] [IsKockLawvere_one R]

open IsKockLawvere_one

lemma cancel_d {b₁ b₂ : R} (h : ∀ (d : D R), b₁ * d = b₂ * d) : b₁ = b₂ := by
  obtain ⟨b1, -, unique1⟩ := isKockLawvere_one (b₁ * · : D R → R)
  obtain ⟨b2, -, unique2⟩ := isKockLawvere_one (b₂ * · : D R → R)
  rw [unique1 b₁ (fun d ↦ by simp), unique2 b₂ (fun d ↦ by simp)]
  exact unique2 _ (fun d ↦ by simp [(h d).symm, unique1 b₁ (fun d ↦ by simp)])

lemma cancel_d_fun {b₁ b₂ : R} : ∀ (k : ℕ),
  (∀ (d : Fin k → D R),
    b₁ * FinChoiceFree.prod k (fun i => (d i).1) =
      b₂ * FinChoiceFree.prod k (fun i => (d i).1)) → b₁ = b₂
| 0 => fun h ↦ by
    simpa only [FinChoiceFree.prod_zero, mul_one] using h (fun i => Fin.elim0 i)
| k + 1 => fun h ↦ by
  refine cancel_d_fun k (fun D ↦ cancel_d (fun d ↦ ?_))
  have h' := h (FinChoiceFree.snoc k D d)
  simpa only [FinChoiceFree.prod_snoc_apply, mul_assoc] using h'

variable (R) in
lemma D_ne_zero : ¬(∀ d ∈ D R, d = 0) := by
  intro h
  obtain ⟨b, hb, hbunique⟩ := isKockLawvere_one (fun _ ↦ (0 : R))
  exact one_ne_zero <| hbunique 0 (by simp) ▸ hbunique 1 (fun ⟨d, hd⟩ ↦ by simp [h _ hd])

end SDG
