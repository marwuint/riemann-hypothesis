import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

namespace GlobalTheory.LineOffT

theorem exists_place (E : Type) [Field E] [NumberField E] {T : ℕ} (hT : T.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ P.asIdeal := by
  have hne : Ideal.span {(T : 𝓞 E)} ≠ ⊤ := fun h => by
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases (Nat.pow_eq_one.1 h1) with h2 | h2
    · exact hT.one_lt.ne' h2
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (T : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => Nat.cast_ne_zero.2 hT.ne_zero (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

variable {D : D7}

theorem isU_nat {x : GlobalTheory.FinPl.Pl D} {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ x.asIdeal) : IsU x (incA D (N : D.host.E)) := by
  have h0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => hN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  refine IsU.of_pres (inU _ h0).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul]
    exact isIntegral_natCast _
  · refine UnitAt.incA_mul_mem_intAt (c := (N : D.host.E)⁻¹) (N := (N : ℤ)) (by rwa [Int.cast_natCast]) ?_
    rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel₀ h0]
    exact isIntegral_one

theorem isU_xi_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : IsU x (xiU D : AE D) := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine IsU.of_pres (xiU D).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0) (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact UnitAt.notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0⁻¹) (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

theorem isU_alpha_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal) (h2 : T ∉ D.host.small)
    (hq : T ≠ D.host.q) (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T)
    {L : Formalism.BasicNotions.TH.HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) : IsU x (α : AE D) := by
  have h := UnitAt.latA_eq_latV (UnitAt.notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (UnitAt.notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)
  obtain ⟨e, he, hg⟩ := line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 x
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

end GlobalTheory.LineOffT

end
