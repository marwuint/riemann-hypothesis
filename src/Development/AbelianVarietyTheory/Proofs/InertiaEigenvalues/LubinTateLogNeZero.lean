import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open scoped Formalism.Per

namespace GlobalTheory.LogFirstOrder

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

abbrev Q : Type := AK K ⧸ RingHom.ker (thetaK K) ^ 2

variable {K}

theorem l_ne_zero_OC : ((l : ℕ) : Per.OC l) ≠ 0 := by
  intro h
  apply GlobalTheory.RingBasics.p_ne_zero (p := l)
  rw [← map_natCast (algebraMap (Per.OC l) ℂ_[l]), h, map_zero]

theorem theta_eq_zero_of_pow_mul {n : ℕ} {c : AK K} (h : thetaK K ((l : AK K) ^ n * c) = 0) : thetaK K c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ l_ne_zero_OC)

theorem eq_zero_OC {t : Per.OC l} (h : ∀ n : ℕ, ((l : ℕ) : Per.OC l) ^ n ∣ t) : t = 0 :=
  GlobalTheory.DiscEval.eq_zero_of_dvd (p := l) h

variable (K) in
theorem exists_gen : ∃ η : AK K, RingHom.ker (thetaK K) = Ideal.span {η} := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (thetaK K (inO K π))
  exact ⟨_, ker_thetaK hπ (hp.trans (thetaK_inO π))⟩

theorem step {η : AK K} (hI : RingHom.ker (thetaK K) = Ideal.span {η}) (hη : η ≠ 0) {a c d : AK K} {n : ℕ}
    (h : η * a = (l : AK K) ^ n * c + η ^ 2 * d) : ∃ c', a = (l : AK K) ^ n * c' + η * d := by
  have hθη : thetaK K η = 0 := by
    have : η ∈ RingHom.ker (thetaK K) := by rw [hI]; exact Ideal.mem_span_singleton_self η
    exact this
  have h1 : thetaK K ((l : AK K) ^ n * c) = 0 := by
    have := congrArg (thetaK K) h
    rw [map_mul, hθη, zero_mul, map_add, map_mul (thetaK K) (η ^ 2), map_pow, hθη] at this
    simpa using this.symm
  have hc : c ∈ Ideal.span {η} := by rw [← hI]; exact theta_eq_zero_of_pow_mul h1
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hc
  refine ⟨c', ?_⟩
  have h2 : η * (a - ((l : AK K) ^ n * c' + η * d)) = 0 := by
    rw [← hc'] at h
    linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hη)

theorem theta_eq_zero_of_sq {a : AK K} (h : a ∈ RingHom.ker (thetaK K) ^ 2) : thetaK K a = 0 :=
  RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero h)

theorem mem_sq_of_forall {a : AK K}
    (h : ∀ n : ℕ, ∃ c : AK K, a - (l : AK K) ^ n * c ∈ RingHom.ker (thetaK K) ^ 2) :
    a ∈ RingHom.ker (thetaK K) ^ 2 := by
  obtain ⟨η, hI⟩ := exists_gen K
  have hmem : ∀ z : AK K, thetaK K z = 0 ↔ η ∣ z := fun z => by
    rw [← Ideal.mem_span_singleton, ← hI, RingHom.mem_ker]
  have hsq : ∀ z : AK K, z ∈ RingHom.ker (thetaK K) ^ 2 ↔ η ^ 2 ∣ z := fun z => by
    rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  by_cases hη : η = 0
  · have := GlobalTheory.AinfK.complete_l K
    have h0 : a = 0 := GlobalTheory.DiscEval.eq_zero_of_dvd (p := l) fun n => by
      obtain ⟨c, hc⟩ := h n
      rw [hsq, hη, zero_pow two_ne_zero, zero_dvd_iff, sub_eq_zero] at hc
      exact ⟨c, hc⟩
    rw [h0]
    exact zero_mem _
  have h1 : thetaK K a = 0 := eq_zero_OC fun n => by
    obtain ⟨c, hc⟩ := h n
    have := theta_eq_zero_of_sq hc
    rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at this
    exact ⟨_, this⟩
  obtain ⟨b, rfl⟩ := (hmem a).1 h1
  have h2 : thetaK K b = 0 := eq_zero_OC fun n => by
    obtain ⟨c, hc⟩ := h n
    obtain ⟨d, hd⟩ := (hsq _).1 hc
    obtain ⟨c', hc'⟩ := step hI hη (a := b) (c := c) (d := d) (n := n) (by linear_combination hd)
    refine ⟨thetaK K c', ?_⟩
    rw [hc', map_add, map_mul, map_pow, map_natCast, (hmem _).2 (dvd_mul_right η d), add_zero]
  obtain ⟨e, rfl⟩ := (hmem b).1 h2
  exact (hsq _).2 ⟨e, by ring⟩

theorem eq_zero_of_forall_dvd {q : Q K} (h : ∀ n : ℕ, ((l : ℕ) : Q K) ^ n ∣ q) : q = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine Ideal.Quotient.eq_zero_iff_mem.2 (mem_sq_of_forall fun n => ?_)
  obtain ⟨w, hw⟩ := h n
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, hw, sub_self]

omit hl in

theorem precomplete_quot {A : Type} [CommRing A] (J : Ideal A) [IsPrecomplete (Ideal.span {(l : A)}) A] :
    IsPrecomplete (Ideal.span {((l : ℕ) : A ⧸ J)}) (A ⧸ J) where
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hf ⊢
    choose e he using fun n => hf (Nat.le_succ n)
    choose e' he' using fun n => Ideal.Quotient.mk_surjective (e n)
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f 0)
    have hf' : ∀ n, f n = Ideal.Quotient.mk J (g - ∑ k ∈ Finset.range n, (l : A) ^ k * e' k) := fun n => by
      induction n with
      | zero => simp [hg]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← sub_sub, map_sub, ← ih, map_mul, map_pow, map_natCast, he', ← he]
        ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : A)})
      (fun n => g - ∑ k ∈ Finset.range n, (l : A) ^ k * e' k) fun {m n} hmn => by
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton]
        rw [sub_sub_sub_cancel_left, ← Finset.sum_Ico_eq_sub _ hmn]
        exact Finset.dvd_sum fun k hk => (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1).mul_right _
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hL
    refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
    have := map_dvd (Ideal.Quotient.mk J) (hL n)
    rwa [map_pow, map_natCast, map_sub, ← hf'] at this

variable (K)

instance complete_quot : IsAdicComplete (Ideal.span {((l : ℕ) : Q K)}) (Q K) :=
  have := GlobalTheory.AinfK.complete_l K
  { precomplete_quot (l := l) (RingHom.ker (thetaK K) ^ 2) with
    haus' := fun q hq => eq_zero_of_forall_dvd fun n => by
      have := hq n
      rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this }

end GlobalTheory.LogFirstOrder
