import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def Pol (c : Bool) {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ χ : HChar (maximalRealSubfield E), GlobalTheory.ContraPair.PolarizedPair π χ ∧ (c = true → χ = quadChar E ^ a)

abbrev Rel (a : ℕ) : Type 1 :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    CuspSub K a → CuspSub M a → Prop

structure Rel.Tower {a : ℕ} (R : Rel a) : Prop where
  refl : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (π : CuspSub K a), R K K π π
  layer : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLiftUnr π P → R K M π P
  trans : ∀ (K M L : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field L] [NumberField L]
    [IsCMField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (π : CuspSub K a) (P : CuspSub M a)
    (U : CuspSub L a), R K M π P → R M L P U → R K L π U

end UpperTheory.Gal.AbelianGaloisNormality
