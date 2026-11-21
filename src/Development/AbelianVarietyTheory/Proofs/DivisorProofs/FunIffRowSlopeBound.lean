import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientNormSquareData

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.RowSlopeCompare

open Formalism.DivisionValues Formalism.L2.Indef GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Same

variable {Bs : DefBase K} {Df : DefSide Bs} {κ : Bs.Tup → Type} [∀ t, Fintype (κ t)]
  [∀ t, DecidableEq (κ t)] {τ : Type} {m : ℕ}

structure Same (S : IndefData Df) (D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m)
    (e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)) (σ : Fin m ≃ Bs.J) : Prop where

  ref : D.t₀ = Bs.μ0

  tup : D.tup = S.μ

  inj : ∀ t, Function.Injective (e t)

  good : ∀ t, LinearMap.range (e t) = D.V₀ t

  lat : ∀ t, (Df.Mt t).map ((e t).restrictScalars (𝓞 K)) = D.M t ⊓ (D.V₀ t).restrictScalars (𝓞 K)

  iota : ∀ t F, D.psi.mulVec ((S.ι t).mulVec ((Df.Pq t).mulVec F)) =
    (((D.r t)⁻¹ : Kˣ) : K) • (D.v t).mulVec (e t F)

  part : D.part = S.Ep

  lam : ∀ p j c, D.lam p j c = S.lam (σ j) Bs.μ0 c p

  kap : D.kap = S.κ

  frame : D.XE = S.XE

variable {S : IndefData Df} {D : RowData K Bs.Tup κ τ (Fin S.D) Bs.Ix m}
  {e : ∀ t, (Fin (Df.nV t) → K) →ₗ[K] (κ t → K)} {σ : Fin m ≃ Bs.J}

end Same

end GlobalTheory.RowSlopeCompare
