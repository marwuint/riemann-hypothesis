import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EpsMeasFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsTowerCompatibleStatement
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.LocalFields.LocalZetaEpsilon
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.TateLocalFactor

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

structure Term {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle) : Type 1 where
  L : Type
  [instField : Field L]
  [instNF : NumberField L]
  [instAlg : Algebra L Ω]
  [instCl : IsAlgClosure L Ω]
  [instKL : Algebra K L]
  [instTow : IsScalarTower K L Ω]
  v' : HeightOneSpectrum (𝓞 L)
  h' : IsPlaceOver A v'
  loc : IsLocalExt L h
  ψ' : AddChar (v'.adicCompletion L) Circle
  cont : Continuous ψ'
  ne : ψ' ≠ 1
  tr : ∀ z : L, ψ' (algebraMap L _ z) = ψ (algebraMap K _ (Algebra.trace K L z))
  a : Weil h' →* (v'.adicCompletion L)ˣ
  ha : IsLocalArtin h' a
  χ : (v'.adicCompletion L)ˣ →* ℂˣ
  hχ : IsSmoothChar χ
  c : ℤ
  x : WD h
  x₀ : WD h
  ix : Induces (WD.lpOfChar h' (χ.comp a) (ha.smooth hχ)) x
  ix₀ : Induces (WD.lpOfChar h' ((1 : (v'.adicCompletion L)ˣ →* ℂˣ).comp a)
    (ha.smooth (isSmoothChar_of_isUnram fun _ _ => rfl))) x₀
  e : ℂˣ
  e₀ : ℂˣ
  he : IsTateMeas ψ' 1 χ e
  he₀ : IsTateMeas ψ' 1 1 e₀

attribute [instance] Term.instField Term.instNF Term.instAlg Term.instCl Term.instKL Term.instTow

section Pres

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}
  {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle}

def Term.pos (T : Term h ψ) (σ : Weil h) : ℂ[X] :=
  T.x.charPol σ ^ T.c.toNat * T.x₀.charPol σ ^ (-T.c).toNat

def Term.neg (T : Term h ψ) (σ : Weil h) : ℂ[X] :=
  T.x₀.charPol σ ^ T.c.toNat * T.x.charPol σ ^ (-T.c).toNat

def Term.val (T : Term h ψ) : ℂˣ := (T.e / T.e₀) ^ T.c

end Pres

end PositivityTheory.Pf1.LocalLanglands.TateLocalFactor

end
