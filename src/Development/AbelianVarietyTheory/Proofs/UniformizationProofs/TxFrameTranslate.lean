import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ShortestVectorStrictOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaAverage
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_translate {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀) (hadd : g.IsAdd g₀ g') :
    g'.b = g.b ∧ ∀ χ z J, Good D.P.L z J → (val (g'.s χ) (𝟙 _) z J).val =
      cstH z (t (Multiplicative.ofAdd χ)).val * (val (g.s χ) (𝟙 _) z J).val := by
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  rw [ht.1, _root_.mul_one] at hb
  refine ⟨hb, fun χ z J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have e := hs χ z J hJ
  have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
  rw [e₀, _root_.mul_one] at e
  rw [e, Units.val_mul, ht.2 χ z J hJ, cst_eq, mul_comm]

theorem coef_translate {k : ℕ} {t : Multiplicative D.X →* Fˣ} {g g₀ g' : GtPtF D F} (ht : IsTor t g₀)
    (hadd : g.IsAdd g₀ g') {w : Frm D F k g.b} (hw : w.IsGen) {w' : Frm D F k g'.b} {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cstH z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g' w' χ = c * (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  obtain ⟨hb, hs⟩ := val_translate ht hadd
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hv z J hJ, hs χ z J hJ, e₁]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * cstH z (t (Multiplicative.ofAdd χ)).val * a

end Frames

attribute [local instance] gtGroup

end GlobalTheory.UT.ThetaAverage
end
