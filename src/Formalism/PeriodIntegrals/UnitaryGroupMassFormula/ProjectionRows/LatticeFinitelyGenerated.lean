import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndexDeterminant.NegLogValuation

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

section ConjP

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def starO (K : Type) [Field K] [NumberField K] [StarRing K] : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)

lemma starO_coe (a : 𝓞 K) : ((starO K a : 𝓞 K) : K) = star (a : K) := rfl

end ConjP

section Idx

open Formalism.HermitianLatticesTheory

variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']

lemma mem_locP' (p : Ideal R) [p.IsPrime] {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

end Idx

section Gam

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def combo {d : ℕ} (y : Fin d → V) : (Fin d → K) →ₗ[K] V where
  toFun c := ∑ i, c i • y i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
    smul_smul]

lemma combo_apply {d : ℕ} (y : Fin d → V) (c : Fin d → K) : combo y c = ∑ i, c i • y i := rfl

end Gam

end PI.DvRows
