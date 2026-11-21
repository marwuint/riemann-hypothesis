import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue GlobalTheory.CechPic
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)

namespace GlobalTheory

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
  {E E' : X.Modules} {r : ℕ}

theorem isometric_det_map {h : VMetric p E r} (H : h.IsCInf) (φ : E ≅ E') :
    (det H).Isometric (det (H.map φ)) :=
  HermLB.isometric_of_chart (L := det H) (M := det (H.map φ)) (fun c : Chart E r => c.map φ)
    (fun _ => le_rfl)
    (fun x c c' _ _ => congrArg (gm (𝟙 X) x _)
      (IsFrame.detUnit_map_iso c.isFrame c'.isFrame φ.hom _ _).symm)
    fun σ c _ hy => congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).map_G φ c hy)

theorem isometric_det_pull {h : VMetric p E r} (H : h.IsCInf) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (det (H.pull π hπ)).Isometric ((det H).pull π hπ) := by
  have := h.isVB.isQuasicoherent
  refine HermLB.isometric_of_local (L := det (H.pull π hπ)) (M := (det H).pull π hπ)
    (fun c : Chart E r => π ⁻¹ᵁ c.U) (fun x => ?_) (fun c _ => c) (fun c => c.pull h.isVB π)
    (fun _ _ h => mem_pull.2 h) (fun _ => le_rfl) (fun _ => 1) (fun x c c' hc hc' => ?_)
    fun σ c y hy => ?_
  · exact exists_chart h.isVB.isLB_det (π x)
  · have e₁ := gm_pull_g (VB.det E r) π (𝟙 Y) x (fun _ => c) (fun _ => c') (mem_pull.2 hc)
      (mem_pull.2 hc')
    have e₂ := gm_pull (𝟙 Y) π x (c.U ⊓ c'.U) ⟨hc, hc'⟩ ((VB.det E r).g c c')
    have e₃ : (VB.det _ r).g (c.pull h.isVB π) (c'.pull h.isVB π) =
        pullU π (c.U ⊓ c'.U) ((VB.det E r).g c c') := by
      refine Units.ext ((IsFrame.val_detUnit_pullback c.isFrame c'.isFrame π inf_le_left
        inf_le_right (T := π ⁻¹ᵁ (c.U ⊓ c'.U)) le_rfl).trans ?_)
      rw [Scheme.Hom.appLE_eq_app]
      rfl
    have e₄ := e₁.trans (e₂.symm.trans (congrArg (gm (𝟙 Y) x _) e₃.symm))
    rw [map_one, map_one, mul_one]
    exact (mul_inv_eq_one.2 e₄).symm
  · rw [logSq_one hy, add_zero]
    refine (((det H).φ σ).pull_φ π hπ _ y).trans ?_
    exact congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => -Real.log M.det.re)
      ((h.met σ).pull_G π hπ c hy).symm

end VMetric

end GlobalTheory
