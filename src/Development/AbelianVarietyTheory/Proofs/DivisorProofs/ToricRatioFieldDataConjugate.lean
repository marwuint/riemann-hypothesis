import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DistributionRelationObj

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmARatio

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host

theorem twisted_value {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (𝓞 E))} {χ ξ : HChar E}
    {Λ : ℂ → ℂ} {m : ℕ} (hU : UnramFin E) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q))
    (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hm : m ≠ 0) (hord : ξ.OrderDvd m) (htr : TrivOnF ξ) (htame : ∀ v, ξ.TameAt v)
    (hram : ∀ v, ξ.UnrAt v ↔ v ∉ Q) (hΛ : IsHeckeL (χ * ξ) Λ) :
    ∃ (ψc : PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) (T : (PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) → ℂ),
      (∀ y, finPart ξ y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 (belowSet Q)) χ ψ (T ψ)) ∧ Λ s = T ψc := by
  classical
  have hp : ∀ x, ξ.1 x ^ m = 1 := fun x => by
    have := congrArg (fun c : HChar E => c.1 x) hord
    simpa using this
  have hχu : ∀ v ∈ belowSet Q, ∀ P, Over P v → χ.UnrAt P := fun v hv P hP => by
    have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rwa [expIn, multiplicity_eq_zero.2 (hQ v hv).2, expAt_zero_iff] at e
  have hξu : ∀ v ∉ belowSet Q, ∀ P, Over P v → ξ.UnrAt P := fun v hv P hP =>
    (hram P).2 fun h => hv (Finset.mem_image.2 ⟨P, h, HeightOneSpectrum.ext hP⟩)
  have hv : IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
    refine ⟨hχ.1.mul (GlobalTheory.ToricDistribution.isUnitary_of_pow hm hp), hχ.2.1.mul htr, fun k => ?_,
      fun v P hP => ⟨fun hv => ?_, fun hv n => ?_⟩⟩
    · rw [HChar.inf_mul, GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one]
      exact hχ.2.2.1 k
    · intro x hx hx1
      rw [HChar.loc_mul, hχu v hv P hP x hx, htame P x hx hx1, one_mul]
    · rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) n]
      refine forall_congr' fun x => forall_congr' fun hx => ?_
      rw [HChar.loc_mul, hξu v hv P hP x hx, mul_one]
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have hex : ∀ q : HeightOneSpectrum (OF E), ∃ P, q ∈ belowSet Q → P ∈ Q ∧ Over P q := fun q => by
    by_cases e : q ∈ belowSet Q
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 e
      exact ⟨P, fun _ => ⟨hP, over_below P⟩⟩
    · exact ⟨P₀, fun h => absurd h e⟩
  choose Pq hPq using hex
  have t := GlobalTheory.ToricDistributionObj.toricSumFormula_holds E I φ hφ s κ 𝔣 (belowSet Q) (χ * ξ) Pq Λ hU hs hb hQ hv
    (fun q hq => (hPq q hq).2) hΛ
  rw [Finset.filter_false_of_mem, Finset.prod_empty, mul_one] at t
  swap
  · intro q hq h
    refine (hram (Pq q)).1 (fun x hx => ?_) (hPq q hq).1
    have := h x hx
    rwa [HChar.loc_mul, hχu q hq _ (hPq q hq).2 x hx, one_mul] at this
  have hker : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ (finPart ξ).ker := by
    refine sup_le ?_ fun y hy => ?_
    · rintro _ ⟨k, rfl⟩
      have := finPart_mul_inf ξ k
      rwa [GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one] at this
    · refine GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level htr (fun v => ?_) hy
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P _ => htame P⟩
        rw [pow_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
      · exact ⟨0, by rw [pow_zero]; exact one_dvd _, fun P hP => (ξ.unrAt_iff P).1 (hξu v hv P hP)⟩
  have hψ : ∀ y, finPart ξ y = QuotientGroup.lift _ (finPart ξ) hker (QuotientGroup.mk y) := fun _ => rfl
  obtain ⟨hfin, S, hS, hT⟩ := (isTwistedSum_iff_isToricSum hψ _).2 t
  exact ⟨_, fun ψ => ∑ᶠ q : PicO (condQ 𝔣 (belowSet Q)), ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0, hψ,
    fun ψ => ⟨hfin, S, hS, rfl⟩, hT⟩

theorem dvd_cond0 {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (v : HeightOneSpectrum (OF D.host.E))
    (h : v.asIdeal ∣ GlobalTheory.FunObj.SqNum.condF P) : v.asIdeal ∣ GlobalTheory.LamTie.cond0 D.host (P.w P.v0) := by
  obtain ⟨u, hu, hd⟩ := (v.prime.dvd_finset_prod_iff _).1 h
  have e : v = u := HeightOneSpectrum.ext
    (associated_iff_eq.1 ((v.irreducible.dvd_irreducible_iff_associated u.irreducible).1 (v.prime.dvd_of_dvd_pow hd)))
  subst e
  rcases P.mem_S0_of_sum_eq.1 hu with h0 | h1
  · have e : below (P.w P.v0) = v := (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))).trans h0.symm
    unfold GlobalTheory.LamTie.cond0
    rw [e]
    exact dvd_mul_left _ _
  · refine Dvd.dvd.mul_right (Dvd.dvd.pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    push_cast
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1 with h | h | h | h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.ThmARatio

end
