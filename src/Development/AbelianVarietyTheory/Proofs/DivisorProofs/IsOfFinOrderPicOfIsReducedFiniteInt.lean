import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder

namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := _root_.GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes B
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine _root_.GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom B _ φ n hinj hn hmul M ?_
  refine _root_.GlobalTheory.pic_pi_isOfFinOrder _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact _root_.GlobalTheory.pic_isOfFinOrder_of_finite_int _ N

end GlobalTheory.PicReducedTors
