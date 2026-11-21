import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8CubicalEvenPolarization
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := _root_.GlobalTheory.PowE8.exists_cp_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := _root_.GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := _root_.GlobalTheory.Mum.exists_preU_even V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := _root_.GlobalTheory.Mum.thetaNZ_of_preU V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
