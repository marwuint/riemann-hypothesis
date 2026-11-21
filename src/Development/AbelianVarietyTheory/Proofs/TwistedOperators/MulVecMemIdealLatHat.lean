import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LevelGroupLifts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingDeterminantRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitConst

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem isMatch_symm {X X' : Data E r} {a : GL (Fin r) E} (h : IsMatch X X' a) : IsMatch X' X a⁻¹ := by
  have e : ∀ v : Fin r → E, (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨h.psi.symm, h.p0.symm, h.xi.symm, fun u v => by rw [← h.iso, e, e], fun v => by rw [h.lat, e]⟩

theorem isMatch_trans {X X' X'' : Data E r} {a b : GL (Fin r) E} (h : IsMatch X X' a) (h' : IsMatch X' X'' b) :
    IsMatch X X'' (b * a) :=
  ⟨h.psi.trans h'.psi, h.p0.trans h'.p0, h.xi.trans h'.xi,
    fun u v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h'.iso, h.iso],
    fun v => by rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← h'.lat, h.lat]⟩

omit [NumberField E] [IsCMField E] in
theorem lact_cast_lact {Ψ Ψ' Ψ'' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (h' : Ψ' = Ψ'') (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact b (castFr h' (lact a (castFr h x))) = lact (b * a) (castFr (h.trans h') x) := by
  subst h h'
  funext τ
  show (b : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((b * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one_cast {Ψ : Finset (E →+* ℂ)} (h : Ψ = Ψ) (x : Frame Ψ r) : lact 1 (castFr h x) = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

variable {U : Formalism.L2.PjFree.Unf Xo c σ r} {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}

def ExactAt (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) : Prop :=
  ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ),
    ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom,
        Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x))

theorem rdU_eq_of_comp_eq (hE : ∀ k, ExactAt U k) (hs : ρ ≫ Xo.s = Xo.s) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n) (hf' : f' ∈ sec Xo c w n)
    (hv : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y')
    {k k' : U.Comp} {δ : GL (Fin r) E} {h : IsMatch (U.X k) (U.X k') δ} (hk : k' = k) (m : MoveMatch U U k k' h ρ ν)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k' (lact δ (castFr h.psi x)) := by
  subst hk
  exact hE _ δ h ρ ν hs m w n hD f hf f' hf' hv x hx

end Free

section Lifts

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
open GlobalTheory.Member (FinCong)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem halfVec_eq_smul (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • z := rfl

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

end Lifts

section Main

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts GlobalTheory.GeoLevel GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem one_le_rank (h : LawsJ T) (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  have hp := h.pins
  rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
  have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
  simp only [Ranks.sigW]; omega

end Main

end GlobalTheory.UnitConst
