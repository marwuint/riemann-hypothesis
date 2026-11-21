import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMulTorsMemLatticeIff

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := _root_.GlobalTheory.IntLatMul.main d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact _root_.GlobalTheory.JInt.main Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.WpFam.TauVal.main Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ c τ hτ).1
    refine _root_.GlobalTheory.CMSize.main l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
