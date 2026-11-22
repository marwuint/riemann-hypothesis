import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralModelOfGaloisStableTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortOfSixUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCube
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := _root_.GlobalTheory.valuation_twelfth_power_of_cube p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (_root_.GlobalTheory.CMModel.LatticeJInt.main L (sqrtNegNat p) hD.mul hβ)
      exact _root_.GlobalTheory.CMModel.modelAt_short_of_six_unit V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := _root_.GlobalTheory.CMModel.exists_stable_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact _root_.GlobalTheory.CMModel.modelAt_of_stable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := _root_.GlobalTheory.CMModel.card_sq_mod_prime p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact _root_.GlobalTheory.CMModel.modelAt_of_stable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((_root_.GlobalTheory.CMModel.sqProd_sq_mem_and_stable p F L t hp hp4 hp3 hD).2 hQ)
      (_root_.GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
