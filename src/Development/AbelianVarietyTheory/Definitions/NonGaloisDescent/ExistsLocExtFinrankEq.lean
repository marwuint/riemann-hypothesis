import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {v : HeightOneSpectrum (𝓞 K)}

def trW {h : IsPlaceOver A v} (x : WD h) (σ : Weil h) : ℂ :=
  LinearMap.trace ℂ _ ((Classical.choose (Classical.choose_spec x.exists_rep)).ρ σ)

open Classical in

def tateEps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (χ : kˣ →* ℂˣ) : ℂ :=
  if hx : ∃ e, IsTateEps ψ χ e then hx.choose else 1

structure LocExt (h : IsPlaceOver A v) where

  L : Type
  [fld : Field L]
  [nf : NumberField L]
  [alg : Algebra L Ω]
  [cl : IsAlgClosure L Ω]
  [algK : Algebra K L]
  [tow : IsScalarTower K L Ω]

  v' : HeightOneSpectrum (𝓞 L)

  h' : IsPlaceOver A v'

  loc : IsLocalExt L h

attribute [instance] LocExt.fld LocExt.nf LocExt.alg LocExt.cl LocExt.algK LocExt.tow

open Classical in

def indOf {h : IsPlaceOver A v} (E : LocExt h) (ξ : Weil E.h' →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) : WD h :=
  if hy : ∃ y : WD h, Induces (WD.lpOfChar E.h' ξ hξ) y then hy.choose else WD.lpZero h

structure BTerm (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion K) Circle) where

  E : LocExt h

  ψ' : AddChar (E.v'.adicCompletion E.L) Circle

  cont : Continuous ψ'

  tr : ∀ z : E.L, ψ' (algebraMap E.L _ z) = ψ (algebraMap K _ (Algebra.trace K E.L z))

  a : Weil E.h' →* (E.v'.adicCompletion E.L)ˣ

  ha : IsLocalArtin E.h' a

  χ : (E.v'.adicCompletion E.L)ˣ →* ℂˣ

  hχ : IsSmoothChar χ

  n : ℤ

variable {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle}

theorem isSmooth_one {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {w : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A w) : GlobalTheory.WeilDeligne.IsSmooth (1 : Weil h →* ℂˣ) :=
  .of_trivial fun _ => rfl

def BTerm.indChi (t : BTerm h ψ) : WD h := indOf t.E (t.χ.comp t.a) (t.ha.smooth t.hχ)

def BTerm.indOne (t : BTerm h ψ) : WD h := indOf t.E 1 (isSmooth_one t.E.h')

def val (l : List (BTerm h ψ)) : ℂ := (l.map fun t => (tateEps t.ψ' t.χ / tateEps t.ψ' 1) ^ t.n).prod

end Defs

end GlobalTheory.DelEps

end
