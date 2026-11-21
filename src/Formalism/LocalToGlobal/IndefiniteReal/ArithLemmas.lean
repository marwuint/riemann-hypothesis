import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.LatticeGeometry.FormsK

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo

namespace Formalism.IndefR.Arith

section Comparison₂

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
variable (P : FormsPkg D G NW CompW algW PtY) [Algebra P.KO D.what₂.LL]
variable {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module P.KO WL] [IsScalarTower P.KO D.what₂.LL WL]
  [Module (𝓞 P.KO) WL] [IsScalarTower (𝓞 P.KO) P.KO WL]
variable {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

def NormTie (pos : (D.what₂.LL →+* ℂ) → Prop) (c : ℝ) {j : ℕ} {w : WeightFamilies.Wt D j} (A : FormsL D.what₂.LL P.KO WL W G0)
    (ι : P.Cusp j w →ₗ[P.KO] WL) : Prop :=
  ∀ σ, pos σ → ∀ F, A.nrmAt σ (ι F) = c * P.l2NormAlt j w (σ.comp P.kL) F

theorem NormTie.rigid {pos : (D.what₂.LL →+* ℂ) → Prop} {c : ℝ} (hc : 0 < c) {j : ℕ} {w : WeightFamilies.Wt D j}
    {A : FormsL D.what₂.LL P.KO WL W G0} {ι : P.Cusp j w →ₗ[P.KO] WL} (h : NormTie P pos c A ι) {a : D.what₂.LL}
    (h' : ∀ σ, pos σ → ∀ F, ‖A.j σ (a • ι F)‖ = c * P.l2NormAlt j w (σ.comp P.kL) F)
    {F : P.Cusp j w} (hF : F ≠ 0) {σ : D.what₂.LL →+* ℂ} (hσ : pos σ) : ‖σ a‖ = 1 := by
  have h1 := h σ hσ F
  have h2 := h' σ hσ F
  rw [map_smulₛₗ, norm_smul] at h2
  unfold FormsL.nrmAt at h1
  have h3 : c * P.l2NormAlt j w (σ.comp P.kL) F ≠ 0 :=
    mul_ne_zero hc.ne' fun e => hF ((P.l2Norm_eq_zero_iff _ _ _ _).1 e)
  rw [h1] at h2
  exact mul_right_cancel₀ h3 (h2.trans (one_mul _).symm)

end Comparison₂

end Formalism.IndefR.Arith
