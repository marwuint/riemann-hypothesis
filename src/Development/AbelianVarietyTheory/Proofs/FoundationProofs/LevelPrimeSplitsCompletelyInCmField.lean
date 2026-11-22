import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SplitColumnClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

noncomputable section

namespace GlobalTheory.ColClassCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

section Descent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p : ℕ}

theorem unram_card_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : Ideal (𝓞 F)) [hv : v.IsPrime] (hpv : (p : 𝓞 F) ∈ v) :
    (p : 𝓞 F) ∉ v ^ 2 ∧ Nat.card (𝓞 F ⧸ v) = p := by
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (v.primesOver (𝓞 E)))
  have hgP : (p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv
  obtain ⟨hP2, hP3⟩ := GlobalTheory.LocSplit.split_prime hp h P hgP
  refine ⟨fun h2 => hP2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]
      exact hpv
    haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    have hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v)) := by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨m, hm⟩ := hP3 (algebraMap (𝓞 F) (𝓞 E) x)
      refine ⟨(m : ZMod p), ?_⟩
      rw [map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq,
        Ideal.mem_of_liesOver P v]
      simpa using hm
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]

theorem ncard_primesOver_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'
  have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hs := Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 F) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
  obtain ⟨h2, hc⟩ := unram_card_of_split (E := E) hp h q hpq
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1 := by
    by_contra hne1
    refine h2 ?_
    have := (Ideal.ramificationIdx'_ne_one_iff (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hpq)).1 hne1
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at this
    simpa using this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' q hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hc] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end Descent

theorem finrank_F (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.sp.cm.deg2, finrank_host D] at h1
  omega

theorem splitsF_of_splitsCompletely (D : D7) {p : ℕ} (h : SplitsCompletely D.host.E p) : SplitsF D p := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 := ncard_primesOver_of_split (F := D.host.F) hp h
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  · haveI := v.isPrime
    exact (unram_card_of_split hp h v.asIdeal hv).2

theorem levelPrime_mod (D : D7) (u : D.what₂.Word) :
    (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 := by
  obtain ⟨π, -, hn, hm⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hm
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hn0 : 1 ≤ D.host.QS := D.host.QS_pos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d := ⟨_, rfl⟩
  have hM1 : 1 < M := by
    have h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)
    omega
  rw [← hM] at ha ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at ha
  set y : D.host.E := (a : D.host.E) * G with hy
  have hyi : IsIntegral ℤ y := (RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)
  have hπ : (π : D.host.E) = 1 + M * y := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    rw [hy]
    push_cast at this ⊢
    linear_combination -this
  have hci : IsIntegral ℤ (D.conjF y) := hyi.map (D.conjF.toRingHom.toIntAlgHom)
  rw [← D.conjF_eq, hπ, map_add, map_mul, map_one, map_natCast] at hn
  set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M) := by
    have hM0' : (M : D.host.E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ) := by
    have : (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M := by simpa using hn'
    push_cast
    rw [this]
    field_simp
    ring
  have h6 : ((D.mem u).A.T : ℤ) = 1 + M * n := by exact_mod_cast h5
  have h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, h6, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)
  exact_mod_cast h7

theorem levelPrime_splitsCompletely_in_cmField (D : D7) (u : D.what₂.Word) : SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨(D.mem u).A.T_prime,
    (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩

theorem split_g_iff (D : D7) (i : Fin 2) :
    SplitsF D (D.host.g i) ↔ SplitsCompletely D.host.E (D.host.g i) :=
  ⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩

end GlobalTheory.ColClassCompare

end
