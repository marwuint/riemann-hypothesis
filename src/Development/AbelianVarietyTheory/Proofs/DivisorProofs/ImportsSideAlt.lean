import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgTau

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ IsAlgebraic ℚ (jT τ) ∧ IsAlgebraic ℚ (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) ∧ ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), IsAlgebraic ℚ (wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro K _ _ d δ ι 𝔞 Λ c Ω τ hd hδ hlat htau hΩ
  obtain ⟨-, hmul, him, -⟩ := _root_.GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ hd hδ hlat
  have hval := _root_.GlobalTheory.WpFam.TauVal.main Λ c Ω τ htau
  have halg := _root_.GlobalTheory.AlgebraicitySecondEisenstein.main Λ (ι δ) Ω hmul him hΩ
  refine ⟨(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD Λ c τ htau).2 Ω hΩ, ?_, ?_, ?_⟩
  · have hj : IsIntegral ℤ (jT τ) := _root_.GlobalTheory.JInt.main Λ c τ (ι δ) htau hmul him
    exact (hj.tower_top (A := ℚ)).isAlgebraic
  · rw [hval.1]; exact halg.1
  · intro N _ x
    rw [(hval.2 N x).1]
    have hN : (N : ℂ) * (c * tors N τ x) ∈ Λ.lattice := by
      have h1 := ((_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ c τ htau).1 ((N : ℂ) * tors N τ x)).2
        ((_root_.GlobalTheory.WpFam.TorsMem.main N τ).2.2.2.1 x)
      simpa [mul_left_comm] using h1
    exact (halg.2 N (c * tors N τ x) (Nat.pos_of_ne_zero (NeZero.ne N)) hN).1

end GlobalTheory.AlgTau
