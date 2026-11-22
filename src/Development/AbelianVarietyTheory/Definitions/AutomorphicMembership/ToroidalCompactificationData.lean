import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Domain

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)

def coW (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin j) (Fin j) ℂ :=
  (frameCo X hj f τ).toBlocks₁₁ - moeb (frameCo X hj f τ) 0 * (frameCo X hj f τ).toBlocks₂₁

def coOm (f : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin (r - j)) (Fin (r - j)) ℂ := (frameCo X hj f τ).toBlocks₂₂

theorem frameCo_eq (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) :
    frameCo X hj f τ = fromBlocks 1 (moeb (frameCo X hj f τ) 0) 0 1 *
      fromBlocks (coW X hj f τ) 0 (frameCo X hj f τ).toBlocks₂₁ (coOm X hj f τ) := by
  rw [fromBlocks_multiply, coW, coOm]
  conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj f τ)]
  simp [moeb_zero, nonsing_inv_mul_cancel_right _ _ (frameCo_isUnit₂₂ X hj hp hf τ)]

theorem isUnit_coOm (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coOm X hj f τ).det :=
  frameCo_isUnit₂₂ X hj hp hf τ

theorem isUnit_coW (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : f ∈ X.dom) (τ : X.Ψ) : IsUnit (coW X hj f τ).det := by
  have h : IsUnit (frameCo X hj f τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ (det_x0F X τ).isUnit).mul (hf τ).1.isUnit
  rw [frameCo_eq X hj hp hf, det_mul, det_fromBlocks_zero₁₂] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)

theorem hodge_co (hp : X.p0 = r - j) {f : Frame X.Ψ r} (hf : IsOrth X f) (τ : X.Ψ) :
    (coW X hj f τ)ᴴ * (hP (moeb (frameCo X hj f τ) 0))⁻¹ * coW X hj f τ = 1 ∧
      (coOm X hj f τ)ᴴ * hQ (moeb (frameCo X hj f τ) 0) * coOm X hj f τ = 1 := by
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp hf τ
  have h1 := hP_inv_moeb hg (zero_mem_hcDom _ _)
  have h2 := hQ_moeb hg (zero_mem_hcDom _ _)
  rw [jW, e] at h1
  rw [kapQ, e, Matrix.mul_zero, zero_add] at h2
  exact ⟨h1.trans (by simp [hP]), h2.trans (by simp [hQ])⟩

end Frames

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}

instance FinalTheorems.smooth (s : FinalTheorems S κ) : SmoothOfRelativeDimension S.Dw.dim (genStr s.T.Z) := s.T.smooth

abbrev ToroidalCompactificationData (s : FinalTheorems S κ) : Type := OddPrimesWithRootsOfUnity s.T.Z

theorem Sig.mult_psi (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (L.ψ t).1 = j :=
  (if_pos (L.ψ t).2).trans S.p_eq

theorem Sig.mult_conj (S : Sig A N j) (L : CmList A) (t : D.what₂.Tau) : S.Dw.mult (conjEmb (L.ψ t).1) = N - j :=
  (if_neg (GlobalTheory.AllWt.conj_not_mem (L.ψ t))).trans (by have := S.p_eq; have := S.rank_eq; omega)

namespace FinalTheorems

variable (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)

abbrev fd : Data D.host.E N := (s.U κ.σ₀).X k

include s in

theorem j_le : j ≤ N := le_of_isUnf _ s.isUnf S.p_eq

abbrev lab : D.what₂.Tau ≃ (s.fd k).Ψ := cmEquiv _ s.isUnf L.ψ k

theorem p0_eq : (s.fd k).p0 = N - j := first_index_eq_of_unfolded _ s.isUnf S.p_eq k

abbrev zOf (f : (s.fd k).dom) : Pt D.what₂.Tau j (N - j) := domPt (s.fd k) s.j_le (s.lab L k) f.1

def framePt (f : (s.fd k).dom) : CxPts (genStr s.T.Z) κ.σ₀ := cxPt s.T.Z ((s.U κ.σ₀).un k f)

def lieFrame (f : (s.fd k).dom) : EigFrame s.T.Z κ.σ₀ ((s.framePt k f).1 ≫ genι s.T.Z) :=
  cxFrame s.T.Z ((s.U κ.σ₀).un k f)

open Classical in

def frameOver (z : Pt D.what₂.Tau j (N - j)) : (s.fd k).dom :=
  if h : ∃ f, s.zOf L k f = z then h.choose else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩

def toCpt (z : Pt D.what₂.Tau j (N - j)) : CxPts (genStr s.T.Z) κ.σ₀ := s.framePt k (s.frameOver L k z)

theorem zOf_mem (f : (s.fd k).dom) : s.zOf L k f ∈ DomI D.what₂.Tau j (N - j) := domPt_mem _ _ _ (s.p0_eq k) f.2

end FinalTheorems

variable {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (L : CmList A)

def ToroidalCompactificationData.gramW (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin j) (Fin j) ℂ :=
  (x.gram (s.framePt k f) (s.lieFrame k f) (L.ψ t).1).submatrix
    (Fin.cast (S.mult_psi L t).symm) (Fin.cast (S.mult_psi L t).symm)

def ToroidalCompactificationData.gramOm (k : s.Comp) (f : (s.fd k).dom) (t : D.what₂.Tau) : Matrix (Fin (N - j)) (Fin (N - j)) ℂ :=
  ((hodgeC (s.fd k) (s.lab L k) t : ℂ) ^ 2) •
    (dualGram (x.gram (s.framePt k f) (s.lieFrame k f) (conjEmb (L.ψ t).1))).submatrix
      (fun a => Fin.cast (S.mult_conj L t).symm a.rev) (fun a => Fin.cast (S.mult_conj L t).symm a.rev)

structure IsBdOf (B : s.Bd L) : Prop where
  m_eq : ∀ k, (B k).m = x.m
  nrm : ∀ k i, ∀ z ∈ DomI D.what₂.Tau j (N - j), (B k).nrm i z = x.nrm κ.σ₀ (Fin.cast (m_eq k) i) (s.toCpt L k z)
  kae : ∀ k W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j),
    s.toCpt L k z ∈ W → ∀ ξ, ((B k).kae z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ
  cst : ∀ k, (B k).cst = x.cst
  metW : ∀ k f t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metW (s.zOf L k f) t *
    coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t
  metOm : ∀ k f t, (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * (B k).metOm (s.zOf L k f) t *
    coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t

end Domain

end GlobalTheory.ShFam
