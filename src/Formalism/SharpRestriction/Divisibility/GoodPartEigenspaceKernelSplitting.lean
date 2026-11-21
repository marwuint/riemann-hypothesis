import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField

noncomputable section

namespace Formalism.MainNotions.PGAL

open Formalism.BasicNotions NumberField

structure Loc (D : D7) (Z : DivX D) where

  MtjH : ℕ → HLat D.what₂.LL
  MtjH_good : ∀ j, (MtjH j).Good

  jT : ∀ j, (MtjH j).V ≃ₗ[D.what₂.LL] D.what₂.MtL D.what₂.mu0 j

  jT_lat : ∀ j x, x ∈ (MtjH j).L ↔ ∃ c : D.what₂.Mt D.what₂.mu0 j → 𝓞 D.what₂.LL,
    D.what₂.jMt D.what₂.mu0 j (jT j x) =
      ∑ v ∈ (D.what₂.MtLat D.what₂.mu0 j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  jT_norm : ∀ j x, Formalism.HermitianLatticesTheory.normAt (MtjH j).b (MtjH j).X (InfinitePlace.mk D.what₂.embLL) x =
    ‖D.what₂.jMt D.what₂.mu0 j (jT j x)‖

  TT : Type
  hk : ∀ j, TT → Module.End D.what₂.LL (MtjH j).V
  hk_comm : ∀ j t t', Commute (hk j t) (hk j t')
  hkAd : TT → TT

  ix : EigIdx D Z

def SameK (D : D7) (s : D.what₂.LL →+* ℂ) : Prop :=
  ∃ g : D.R.Psi, s.comp D.embE = D.host.emb (g : D.R.GG)

structure CjDat (D : D7) (s : D.what₂.LL →+* ℂ) where

  ga : Equiv.Perm D.what₂.Tau
  ga_def : ∀ τ, (s.comp D.embE).comp
      ((D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG) : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →+* D.host.E) =
    D.host.emb ((D.eTau (ga τ) : D.R.Psi) : D.R.GG)

  MtC : ℕ → Type
  [iMt : ∀ j, NormedAddCommGroup (MtC j)]
  [iMti : ∀ j, InnerProductSpace ℂ (MtC j)]
  [iMtf : ∀ j, FiniteDimensional ℂ (MtC j)]

  MjC : ℕ → Type
  [iMj : ∀ j, NormedAddCommGroup (MjC j)]
  [iMji : ∀ j, InnerProductSpace ℂ (MjC j)]
  [iMjf : ∀ j, FiniteDimensional ℂ (MjC j)]

  thC : ∀ j, MtC j →ₗ[ℂ] MjC j

  eC : ∀ j, MtC j →ₗ[ℂ] MtC j
  eC_idem : ∀ j, eC j ∘ₗ eC j = eC j
  eC_sa : ∀ j, (eC j).IsSymmetric

  isotC : ∀ j, D.what₂.FT → Submodule ℂ (MjC j)

attribute [instance] CjDat.iMt CjDat.iMti CjDat.iMtf CjDat.iMj CjDat.iMji CjDat.iMjf

abbrev CjFam (D : D7) : Type 1 := ∀ s : D.what₂.LL →+* ℂ, SameK D s → CjDat D s

section Rows

variable (D : D7) (Z : DivX D) (E : EigIdx D Z) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  (S : RowSide D EE) (A : AmbForm D S)

structure LocX where
  TX : Type
  hkX : TX → Module.End D.what₂.LL (A.MtH D.what₂.mu0).V
  hkX_comm : ∀ t t', Commute (hkX t) (hkX t')

  hkXAd : TX → TX

  cs : E.Pi → TX → D.what₂.LL

end Rows

end Formalism.MainNotions.PGAL

end
