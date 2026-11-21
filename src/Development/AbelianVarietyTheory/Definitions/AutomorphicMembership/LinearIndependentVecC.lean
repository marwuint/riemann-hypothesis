import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open TopologicalSpace
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open Formalism.L2.Pj (FrPt CAt embK)
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts
open GlobalTheory.AllWt (Psi ptF framesOn LiesOn)
open scoped ComplexOrder

namespace GlobalTheory.TrueCx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}

section Std

variable (X : Data E r) (hj : j ≤ r) (κ : Tau ≃ X.Ψ)

def stdMat (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem frameCo_stdMat (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (stdMat X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  show reindex _ _ (_ * (mat (x0F X) τ * _)) = _
  rw [nonsing_inv_mul_cancel_left _ _ (det_x0F X τ).isUnit]
  simp

theorem domPt_stdMat (z : Pt Tau j (r - j)) : domPt X hj κ (stdMat X hj κ z) = z := by
  funext t
  simp [domPt, frameCo_stdMat, moeb_zero]

theorem stdMat_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    stdMat X hj κ z ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat (x0F X) τ * _).det ≠ 0
    rw [det_mul, det_reindex_self, det_fromBlocks_zero₂₁]
    simpa using det_x0F X τ
  have h0 := congrArg transpose (isOrth_x0F X τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0
  set N : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 (z (κ.symm τ)) 0 1 with hN
  have h1 : reindex (idx hj) (idx hj) (gram τ.1 X.Gm (mat (stdMat X hj κ z) τ))ᵀ = Nᴴ * -Jpq j (r - j) * N := by
    rw [gram_eq_mul, ← reindex_sgn hj, ← h0]
    show reindex _ _ ((mat (x0F X) τ * reindex _ _ N)ᴴ * _ * (mat (x0F X) τ * reindex _ _ N)) = _
    simp only [conjTranspose_mul, reindex_apply, conjTranspose_submatrix, ← submatrix_mul_equiv _ _ _ (idx hj).symm,
      submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id, Matrix.mul_assoc]
  have h2 : (Nᴴ * -Jpq j (r - j) * N).toBlocks₂₂ = hQ (z (κ.symm τ)) := by
    simp [hN, Jpq, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_multiply, hQ, sub_eq_neg_add]
  have h3 : X.gramPos (stdMat X hj κ z) τ = ((hQ (z (κ.symm τ))).submatrix (finCongr hp) (finCongr hp))ᵀ := by
    ext a b
    have e : ∀ a : Fin X.p0, (idx hj).symm (Sum.inr (finCongr hp a)) = Fin.castLE X.p0_le a :=
      fun a => Fin.ext (idx_symm_inr hj _)
    rw [← h2, ← h1]
    simp only [transpose_apply, submatrix_apply, toBlocks₂₂, of_apply, reindex_apply, e, Data.gramPos]
  rw [h3]
  exact (PosDef.submatrix (hz (κ.symm τ)) (finCongr hp).injective).transpose

open Classical in

def stdFrame (hp : X.p0 = r - j) (z : Pt Tau j (r - j)) : X.dom :=
  if h : z ∈ DomI Tau j (r - j) then ⟨stdMat X hj κ z, stdMat_mem X hj κ hp h⟩
  else ⟨stdMat X hj κ 0, stdMat_mem X hj κ hp fun _ => zero_mem_hcDom _ _⟩

theorem stdFrame_val (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    (stdFrame X hj κ hp z).1 = stdMat X hj κ z := by rw [stdFrame, dif_pos hz]

theorem domPt_stdFrame (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    domPt X hj κ (stdFrame X hj κ hp z).1 = z := by rw [stdFrame_val X hj κ hp hz, domPt_stdMat]

end Std

section Tor

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ)

abbrev torC : Scheme.{0} := pullback Y.s (spMap σ)

abbrev torStr : torC Y σ ⟶ Sp ℂ := pullback.snd Y.s (spMap σ)

abbrev torPr : torC Y σ ⟶ Y.X := pullback.fst Y.s (spMap σ)

instance smooth_torStr {D : ℕ} [h : SmoothOfRelativeDimension D Y.s] : SmoothOfRelativeDimension D (torStr Y σ) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange D).of_isPullback (IsPullback.of_hasPullback _ _) h

abbrev TorPts : Type := CxPts (torStr Y σ) (RingHom.id ℂ)

variable {Y σ}

variable (Y)

def ptC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y

def xC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.X := y.x

theorem ptC_fst (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.fst _ _ = xC y := pullback.lift_fst _ _ _

theorem ptC_snd (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.snd _ _ = spMap σ := pullback.lift_snd _ _ _

def torPt (y : FrPt Xo c (CAt σ)) : TorPts Y σ :=
  ⟨pullback.lift (ptC y ≫ Y.j) (spMap (RingHom.id ℂ)) (by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, ptC_snd, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_snd _ _ _⟩

theorem torPt_pr (y : FrPt Xo c (CAt σ)) : (torPt Y y).1 ≫ torPr Y σ = ptC y ≫ Y.j := pullback.lift_fst _ _ _

abbrev LieAt (y : TorPts Y σ) : Type := TanM (y.1 ≫ torPr Y σ) Y.t.G

variable (σ) in

abbrev LieForm : Type := ∀ y : TorPts Y σ, LieAt Y y →ₗ[ℂ] LieAt Y y →ₗ⋆[ℂ] ℂ

def lieEquiv (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] LieAt Y (torPt Y y) :=
  (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Y.m (ptC y) (torPt_pr Y y).symm)

end Tor

end GlobalTheory.TrueCx
