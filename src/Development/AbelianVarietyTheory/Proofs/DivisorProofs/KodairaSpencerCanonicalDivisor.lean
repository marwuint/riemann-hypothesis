import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKSSymPairBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellChartFrameEigenbasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellFramedPointsTriangularFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontal

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

theorem exists_unit_mul {Y : Scheme.{0}} {V : Y.Opens} (y : Y) (hy : y ∈ V) [IsDomain (Y.presheaf.stalk y)]
    (t d : Γ(Y, V)) (h0 : ger y hy t ≠ 0) (h1 : ger y hy t ∣ ger y hy d) (h2 : ger y hy d ∣ ger y hy t) :
    ∃ (V' : Y.Opens) (_ : y ∈ V') (h : V' ≤ V) (b : Γ(Y, V')), (∀ z hz, IsUnit (ger z hz b)) ∧
      resG Y h t = b * resG Y h d := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hu : IsUnit b := by
    refine IsUnit.of_mul_eq_one a (mul_left_cancel₀ h0 ?_)
    calc ger y hy t * (b * a) = (ger y hy t * a) * b := by ring
      _ = ger y hy t * 1 := by rw [← ha, ← hb, mul_one]
  obtain ⟨O, hO, s, rfl⟩ := Y.presheaf.exists_germ_eq b
  have hm : y ∈ V ⊓ O := ⟨hy, hO⟩
  have e : ger y hm (resG Y inf_le_left t) = ger y hm (resG Y inf_le_right s * resG Y inf_le_left d) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG, hb, mul_comm]
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have l₁ : O' ⊓ Y.basicOpen s ≤ V ⊓ O := inf_le_left.trans i₁.le
  refine ⟨O' ⊓ Y.basicOpen s, ⟨hO', (Y.mem_basicOpen s y hO).2 hu⟩, l₁.trans inf_le_left,
    resG Y (l₁.trans inf_le_right) s, fun z hz => ?_, fun_ext_ger fun z hz => ?_⟩
  · rw [ger_resG]
    exact (Y.mem_basicOpen s z _).1 hz.2
  · have e₂ := congrArg (ger z hz.1) e'
    have a₁ := ger_resG i₁.le z hz.1 (resG Y (inf_le_left : V ⊓ O ≤ V) t)
    have a₂ := ger_resG i₂.le z hz.1 (resG Y (inf_le_right : V ⊓ O ≤ O) s * resG Y (inf_le_left : V ⊓ O ≤ V) d)
    have e₃ := a₁.symm.trans (e₂.trans a₂)
    simp only [map_mul, ger_resG] at e₃ ⊢
    exact e₃

theorem ger_ne_zero {Y : Scheme.{0}} {V O : Y.Opens} (hO : Dense (O : Set Y)) (t : Γ(Y, V))
    (h : ∀ z (hz : z ∈ V), z ∈ O → IsUnit (ger z hz t)) (y : Y) (hy : y ∈ V) : ger y hy t ≠ 0 := by
  intro h0
  obtain ⟨O', hO', i₁, i₂, e'⟩ := Y.presheaf.germ_eq y hy hy t 0 (h0.trans (map_zero _).symm)
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty O' O'.isOpen ⟨y, hO'⟩
  have e₂ := congrArg (ger z hz) e'
  have a₁ := ger_resG i₁.le z hz t
  have a₂ := ger_resG i₂.le z hz (0 : Γ(Y, V))
  have e₃ := a₁.symm.trans (e₂.trans a₂)
  rw [map_zero] at e₃
  exact (h z _ hzO).ne_zero e₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem chartFr_congr {TF : TorFlag Xo c} {K : Type} [Field K] [Algebra c.F K] {k : TF.X.F.J} {z z' : Sp K ⟶ TF.X.YY}
    (e : z = z') {hz : ⊤ ≤ z ⁻¹ᵁ TF.X.F.U k} (hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k) {Q : FrPt Xo c K}
    (h : TF.X.F.ChartFr k z hz Q) : TF.X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem det_block {K : Type} [Field K] {m : ℕ} (o : Fin m ≃ HIx Dw (psiSet H))
    (G : (Fin m ⊕ VIx Dw) → TIx Dw (psiSet H) → K) (h0 : ∀ i b, G (.inl i) (.inr b) = 0)
    (h1 : (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b)).det = 1) :
    (Matrix.of fun a b => G (((tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl _))) a) (tanOrd Dw b)).det =
      (Matrix.of fun i j => G (.inl i) (.inl (o j))).det := by
  let e := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let A : Matrix (Fin m ⊕ VIx Dw) (Fin m ⊕ VIx Dw) K := Matrix.fromBlocks
    (Matrix.of fun i j => G (.inl i) (.inl (o j))) 0 (Matrix.of fun a j => G (.inr a) (.inl (o j)))
    (Matrix.of fun a b : VIx Dw => G (.inr a) (.inr b))
  have : (Matrix.of fun a b => G (e a) (tanOrd Dw b)) = A.submatrix e e := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    have hb : tanOrd Dw b = Equiv.sumCongr o (Equiv.refl (VIx Dw)) (e b) := by
      simp only [e, Equiv.trans_apply]
      rcases tanOrd Dw b with k | k <;> simp
    rw [hb]
    rcases e a with i | i <;> rcases e b with j | j <;> simp [A, h0]
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, h1, mul_one]

def diagUnit {R : Type} [CommRing R] (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R)
    (h : ∀ σ i, IsUnit (L σ i i)) : Rˣ :=
  ∏ q : Σ σ : E →+* ℂ, Fin (Dw.mult σ), (h q.1 q.2).unit⁻¹ ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 (some q)

theorem map_diagUnit {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (L : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) R) (h : ∀ σ i, IsUnit (L σ i i)) (t : Ix Dw → Kˣ)
    (ht : ∀ σ i, (t (some ⟨σ, i⟩) : K) * φ (L σ i i) = 1) :
    (∏ ix, t ix ^ AllWt.exOf Dw (FlagTan.kap Dw) 0 ix).val = φ (diagUnit L h).val := by
  change _ = (Units.map (φ : R →* K) (diagUnit L h)).val
  congr 1
  rw [diagUnit, map_prod, Fintype.prod_option, FlagMod.exOf_none, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_zpow, map_inv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (Units.ext (ht q.1 q.2))

end GlobalTheory.LogPole
