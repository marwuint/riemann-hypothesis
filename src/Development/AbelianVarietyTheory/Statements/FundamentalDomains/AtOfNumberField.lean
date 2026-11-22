import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.IsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow

noncomputable section
namespace GlobalTheory.KeyKa

def ConnFam : Prop :=
  ∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S)
    (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧
    (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)

namespace ConnFamTest

def At (x : KeyIn ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S)
    (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧
    (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)

end ConnFamTest
end GlobalTheory.KeyKa
end
