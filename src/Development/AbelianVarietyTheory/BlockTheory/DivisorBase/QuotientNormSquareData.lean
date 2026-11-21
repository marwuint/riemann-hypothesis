import Mathlib
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.ShiftInvariance

open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData

variable {L : Type} [Field L] [NumberField L]

def quotNormSq {κ τ : Type} [Fintype κ] [DecidableEq κ] (X : InfinitePlace L → Matrix κ κ ℂ)
    (V : Submodule L (κ → L)) (A : Matrix τ κ L) (p : InfinitePlace L) (y : τ → L) : ℝ :=
  sInf {s : ℝ | ∃ F ∈ V, A.mulVec F = y ∧ s = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun L κ) X p F ^ 2}

structure RowData (L : Type) [Field L] [NumberField L] (T : Type) (κ : T → Type)
    [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)] (τ ε C : Type) [Fintype ε] [DecidableEq ε]
    (m : ℕ) where

  t₀ : T

  tup : HeightOneSpectrum (𝓞 L) → T
  tup_finite : {w | tup w ≠ t₀}.Finite

  M : ∀ t, Submodule (𝓞 L) (κ t → L)
  M_lattice : ∀ t, Submodule.IsLattice L (M t)

  V₀ : ∀ t, Submodule L (κ t → L)

  v : ∀ t, Matrix τ (κ t) L

  r : T → Lˣ
  r_ref : r t₀ = 1

  X₀ : InfinitePlace L → Matrix (κ t₀) (κ t₀) ℂ
  X₀_unit : ∀ p, IsUnit (X₀ p).det

  psi : Matrix τ ε L
  psi_injective : Function.Injective psi.mulVecLin
  psi_range : LinearMap.range psi.mulVecLin = (V₀ t₀).map (v t₀).mulVecLin

  part : C → Submodule L (ε → L)
  part_span : ⨆ c, part c = ⊤

  lam : InfinitePlace L → Fin m → C → ℝ
  lam_pos : ∀ p j c, 0 < lam p j c

  kap : InfinitePlace L → ℝ
  kap_pos : ∀ p, 0 < kap p

  XE : InfinitePlace L → Matrix ε ε ℂ
  XE_unit : ∀ p, IsUnit (XE p).det
  XE_norm : ∀ p c, ∀ x ∈ part c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun L ε) XE p x ^ 2 =
    kap p * (∏ j, lam p j c) * quotNormSq X₀ (V₀ t₀) (v t₀) p (psi.mulVec x)
  XE_orth : ∀ p c c', c ≠ c' → ∀ x ∈ part c, ∀ y ∈ part c',
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun L ε) XE p x y = 0

namespace RowData

end RowData

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
