import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

namespace GlobalTheory.Glue

variable {T : Scheme.{0}} {F G : T.Modules}

theorem le_iSup_affine (U : T.Opens) :
    U ≤ ⨆ k : {W : T.Opens // IsAffineOpen W ∧ W ≤ U}, k.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩

variable (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V))
  (hj : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(F, V)), j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s))

include hj in

theorem agree {U W W' V : T.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWU : W ≤ U)
    (hW'U : W' ≤ U) (h₁ : V ≤ W) (h₂ : V ≤ W') (s : Γ(F, U)) :
    GlobalTheory.Twist.resM G h₁ (j W hW (GlobalTheory.Twist.resM F hWU s)) =
      GlobalTheory.Twist.resM G h₂ (j W' hW' (GlobalTheory.Twist.resM F hW'U s)) := by
  refine GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ V} => k.1)
    (fun k => k.2.2) (le_iSup_affine V) fun k => ?_
  rw [GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM, ← hj _ _ hW k.2.1, ← hj _ _ hW' k.2.1,
    GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM]

include hj in
theorem exists_glue (U : T.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = j W hW (GlobalTheory.Twist.resM F hWU s) := by
  obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover
    (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (le_iSup_affine U)
    (fun k => j k.1 k.2.1 (GlobalTheory.Twist.resM F k.2.2 s))
    fun k l => agree j hj k.2.1 l.2.1 k.2.2 l.2.2 _ _ s
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

def glue (U : T.Opens) (s : Γ(F, U)) : Γ(G, U) := Classical.choose (exists_glue j hj U s)

end GlobalTheory.Glue

