import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenPsiOfThetaExpansionPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaExpansionFunctionalEquationDegreeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BimultiplicativeTauOfThetaExpansionPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPreUSetPsi
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInMaximalIdealOfNeZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU

theorem exists_degData_fe_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U

  obtain ⟨θ, f, hθ⟩ := _root_.GlobalTheory.ThetaIntegral.exists_theta hL hL2 V hV D A G U
  have hf := (_root_.GlobalTheory.UU.theta_support_eq_univ hL hL2 V hV D A G U θ f hθ).1

  obtain ⟨ψ, h, hpsi⟩ := _root_.GlobalTheory.exists_psi_psiRel hL hL2 V D f hf
  obtain ⟨U', hP, hgen, -, hth⟩ := exists_preU_setPsi V D (IsLocalRing.maximalIdeal V) A G U ψ h
  obtain ⟨θ', hθ'⟩ := hth θ f hθ

  have hev := _root_.GlobalTheory.psiEven_of_psiRel hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hbi := _root_.GlobalTheory.tauBimult_of_psiRel hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  have hfin := _root_.GlobalTheory.psi_tendsto_zero V hV (setPsi D ψ h) A G U' θ' f hθ' (hf 0) hpsi
  have hpos := GlobalTheory.psiIn_maximalIdeal_of_ne_zero V hV (setPsi D ψ h) hbi hev (hfin 1)
  have hfe := _root_.GlobalTheory.UU.fe_one_of_psiRel hL hL2 V hV (setPsi D ψ h) A G U' θ' f hθ' hpsi
  exact ⟨{ toPre := setPsi D ψ h, psi_even := hev, tau_bimult := hbi, psi_pos := hpos, psi_tendsto := hfin }, U', hP, hgen, hfe⟩
end GlobalTheory.UU
