import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

variable {Ω : Type} [Field Ω]

section Galois

variable (k L Ω : Type) [Field k] [Field L] [Field Ω] [Algebra k Ω] [Algebra L Ω] [Algebra k L] [IsScalarTower k L Ω]

def resG : G L Ω →* G k Ω := AlgEquiv.restrictScalarsHom k

variable {L Ω}

open Classical in

def ext0 (χ : G L Ω →* ℂˣ) (σ : G k Ω) : ℂ :=
  if hx : ∃ τ : G L Ω, resG k L Ω τ = σ then ((χ hx.choose : ℂˣ) : ℂ) else 0

def gInd (χ : G L Ω →* ℂˣ) (σ : G k Ω) : ℂ :=
  ∑ᶠ q : G k Ω ⧸ (resG k L Ω).range, ext0 k χ (q.out⁻¹ * σ * q.out)

end Galois

section Hecke

variable {L : Type} [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]

def Matches (χ : G L Ω →* ℂˣ) (X : HeckeCharacter L) : Prop :=
  ∀ (A : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A u) (a : Weil h →* (u.adicCompletion L)ˣ),
    IsLocalArtin h a → ∀ σ : Weil h, localChar X u (a σ) = χ (σ : G L Ω)

open Classical in

def hk (χ : G L Ω →* ℂˣ) : HeckeCharacter L :=
  if hx : ∃ X : HeckeCharacter L, Matches χ X ∧ ∃ N : ℕ, 0 < N ∧ X ^ N = 1 then hx.choose else 1

end Hecke

structure GTerm (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] where

  L : Type
  [fld : Field L]
  [nf : NumberField L]
  [alg : Algebra L Ω]
  [cl : IsAlgClosure L Ω]
  [algK : Algebra k L]
  [tow : IsScalarTower k L Ω]

  χ : G L Ω →* ℂˣ

  op : IsOpen (χ.ker : Set (G L Ω))

  n : ℤ

attribute [instance] GTerm.fld GTerm.nf GTerm.alg GTerm.cl GTerm.algK GTerm.tow

section Global

variable {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

abbrev GTerm.Over (t : GTerm k Ω) (w : HeightOneSpectrum (𝓞 k)) : Type :=
  {u : HeightOneSpectrum (𝓞 t.L) // u.under (𝓞 k) = w}

end Global

section Place

variable {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion K) Circle}

def wfix (E : LocExt h) : Subgroup (Weil h) := (resG K E.L Ω).range.comap (Weil h).subtype

structure FCorr (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (u : HeightOneSpectrum (𝓞 L)) (E : LocExt h) (g : G K Ω)
    (i : u.adicCompletion L ≃+* E.v'.adicCompletion E.L) : Prop where

  cont : Continuous i

  psi : ∀ x, localAdelicChar E.L E.v' (i x) = localAdelicChar L u x

  fix : ∀ σ : Weil h, σ ∈ wfix E ↔ g⁻¹ * (σ : G K Ω) * g ∈ (resG K L Ω).range

  art : ∀ (χ : G L Ω →* ℂˣ) (X : HeckeCharacter L), Matches χ X →
    ∀ a : Weil E.h' →* (E.v'.adicCompletion E.L)ˣ, IsLocalArtin E.h' a →
      ∀ (σ : Weil E.h') (τ : G L Ω) (x : (u.adicCompletion L)ˣ),
        resG K L Ω τ = g⁻¹ * resG K E.L Ω σ * g → Units.map i.toRingHom.toMonoidHom x = a σ → localChar X u x = χ τ

end Place

structure Realises {A : ValuationSubring Ω} {k : Type} [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]
    {w : HeightOneSpectrum (𝓞 k)} {h : IsPlaceOver A w} (t : GTerm k Ω)
    (b : t.Over w → BTerm h (localAdelicChar k w)) (g : t.Over w → G k Ω)
    (i : ∀ u : t.Over w, u.1.adicCompletion t.L ≃+* (b u).E.v'.adicCompletion (b u).E.L) : Prop where

  corr : ∀ u, FCorr t.L u.1 (b u).E (g u) (i u)

  n_eq : ∀ u, (b u).n = t.n

  psi : ∀ u, (b u).ψ' = localAdelicChar (b u).E.L (b u).E.v'

  chi : ∀ u x, (b u).χ (Units.map (i u).toRingHom.toMonoidHom x) = localChar (hk t.χ) u.1 x

  indChi : ∀ σ : Weil h, gInd k t.χ σ = ∑ᶠ u, trW (b u).indChi σ

  indOne : ∀ σ : Weil h, gInd k (1 : G t.L Ω →* ℂˣ) σ = ∑ᶠ u, trW (b u).indOne σ

namespace Inh

end Inh

end GlobalTheory.DelGlob

end
