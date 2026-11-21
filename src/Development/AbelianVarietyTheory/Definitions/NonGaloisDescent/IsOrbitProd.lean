import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

abbrev BCRel : Type 1 :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)),
    IrrGL (v.adicCompletion K) → IrrGL (u.adicCompletion L) → Prop

section Cyc

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def CycAt (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) : Prop :=
  IsGalois K L ∧ (Module.finrank K L).Prime ∧ u.under (𝓞 K) = v ∧
    ∀ u' : HeightOneSpectrum (𝓞 L), u'.under (𝓞 K) = v → u' = u

def Conj {u : HeightOneSpectrum (𝓞 L)} (s : L ≃ₐ[K] L) (Y Y' : IrrGL (u.adicCompletion L)) : Prop :=
  ∃ i : u.adicCompletion L ≃+* u.adicCompletion L, Continuous i ∧
    (∀ x : L, i (algebraMap L _ x) = algebraMap L _ (s x)) ∧ RepRel i Y Y'

variable (L) in

def KillsNorms {v : HeightOneSpectrum (𝓞 K)} (η : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  ∀ (z : L) (y : (v.adicCompletion K)ˣ), (y : v.adicCompletion K) = algebraMap K _ (Algebra.norm K z) → η y = 1

variable (K) in

def IsOrbitProd {u : HeightOneSpectrum (𝓞 L)} (Y : (L ≃ₐ[K] L) → IrrGL (u.adicCompletion L))
    (X : IrrGL (u.adicCompletion L)) : Prop :=
  (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) ∧ Function.Injective Y ∧
    ∃ (g : ℕ) (e : Fin g ≃ (L ≃ₐ[K] L)) (hd : ∑ i, (Y (e i)).1 = X.1), Nonempty (X.rep.Equiv (prodIrr (fun i => Y (e i)) hd))

end Cyc

structure LocalBCAt {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {u : HeightOneSpectrum (𝓞 L)}
    (B : IrrGL (v.adicCompletion K) → IrrGL (u.adicCompletion L) → Prop) : Prop where

  ex : ∀ x, x.IsCusp → ∃! X, B x X

  shape : ∀ x X, x.IsCusp → B x X → X.IsCusp ∨ ((∃ Y, IsOrbitProd K Y X) ∧ ∀ η hη, KillsNorms L η → x.tw η hη = x)

  desc : ∀ X, X.IsCusp → (∀ s : L ≃ₐ[K] L, Conj s X X) → ∃ x, x.IsCusp ∧ B x X

  ind : ∀ Y : (L ≃ₐ[K] L) → IrrGL (u.adicCompletion L), (∀ s, (Y s).IsCusp ∧ Conj s (Y 1) (Y s)) → Function.Injective Y →
    ∃ x X, x.IsCusp ∧ B x X ∧ IsOrbitProd K Y X

  fib : ∀ x x' X, x.IsCusp → x'.IsCusp → B x X → B x' X → ∃ η hη, KillsNorms L η ∧ x' = x.tw η hη

def LocalBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u → LocalBCAt (BC K L v u)

def StrongBC (BC : BCRel) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)), CycAt v u →
    ∀ (n c : ℕ) (π : CuspSub K n) (m : Fin c → ℕ) (P : ∀ i, CuspSub L (m i)), 1 ≤ n → (∀ i, 1 ≤ m i) →
    UpperTheory.V.Published.WeakBC (CG.mk π).HasSat
      (fun w B => ∃ B' : Fin c → Multiset ℂˣ, (∀ i, (CG.mk (P i)).HasSat w (B' i)) ∧ B = ∑ i, B' i) →
    ∀ (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : ∀ i, SmIrr (GL (Fin (m i)) (u.adicCompletion L))),
    π.IsLocComp v τ → (∀ i, (P i).IsLocComp u (T i)) →
    ∀ (t : ℕ) (x : Fin t → IrrGL (v.adicCompletion K)) (X : Fin t → IrrGL (u.adicCompletion L))
      (S : Fin t → Multiset (IrrGL (u.adicCompletion L))) (S' : Fin c → Multiset (IrrGL (u.adicCompletion L))),
    HasSupport τ.ρ (Finset.univ.val.map x) → (∀ j, BC K L v u (x j) (X j) ∧ HasSupport (X j).rep (S j)) →
    (∀ i, HasSupport (T i).ρ (S' i)) → ∑ i, S' i = ∑ j, S j

end GlobalTheory.FunExt

end
