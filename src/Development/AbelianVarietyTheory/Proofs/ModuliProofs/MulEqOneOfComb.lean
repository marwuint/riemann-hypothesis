import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeisLinear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMonomialMatricesProjectiveRep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentThetaBasisGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionGeneratorPower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

instance noeth [ArithBase o Ω] (S : ThetaSys o Ω) : IsNoetherianRing S.R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg S.fg

theorem one_le_rN (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)

structure Agree {S : ThetaSys o Ω} (ρ : S.Real) (Z : Realisation S) : Prop where
  P : ρ.P = Z.P
  n : ρ.n = Z.n
  k : ρ.k = Z.k
  pt : ∀ a, HEq (ρ.pt a) (Z.tor a)
  rig : HEq ρ.rig Z.rig
  θ : HEq ρ.th₁ Z.θ
  s₁ : HEq (ρ.s ρ.i₀) Z.s₁
  b : ∀ i, HEq (ρ.s i) (Z.b i)

end GlobalTheory.RealCompare
end
