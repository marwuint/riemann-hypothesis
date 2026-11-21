import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

noncomputable section

namespace GlobalTheory

open MvPowerSeries

section Eval

variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem aeval_mem_pow_of_mem_idealOfVars {J : Ideal S} {x : σ → S} (hx : ∀ i, x i ∈ J) {n : ℕ}
    {p : MvPolynomial σ A} (hp : p ∈ MvPolynomial.idealOfVars σ A ^ n) :
    MvPolynomial.aeval x p ∈ J ^ n := by
  have h : (MvPolynomial.idealOfVars σ A).map (MvPolynomial.aeval x : _ →ₐ[A] S) ≤ J := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa using hx i
  have := Ideal.mem_map_of_mem (MvPolynomial.aeval x : _ →ₐ[A] S) hp
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

theorem eq_of_forall_sub_mem_ideal_pow (J : Ideal S) [IsHausdorff J S] {x y : S}
    (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n

variable [Finite σ]

def mvEvalMod (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) : MvPowerSeries σ A →ₐ[A] S ⧸ J ^ n :=
  (Ideal.Quotient.liftₐ (MvPolynomial.idealOfVars σ A ^ n)
    ((Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval x)) fun _ hp =>
      Ideal.Quotient.eq_zero_iff_mem.2 (aeval_mem_pow_of_mem_idealOfVars hx hp)).comp
    ((truncTotalAlgHom σ A n).restrictScalars A)

theorem mvEvalMod_apply (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) (n : ℕ)
    (f : MvPowerSeries σ A) :
    mvEvalMod A J x hx n f = Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) := rfl

theorem factor_comp_mvEvalMod (J : Ideal S) (x : σ → S) (hx : ∀ i, x i ∈ J) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (mvEvalMod A J x hx n) =
      mvEvalMod A J x hx m := by
  refine AlgHom.ext fun f => ?_
  change Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal n f)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval x (truncTotal m f))
  rw [Ideal.Quotient.eq, ← map_sub]
  exact aeval_mem_pow_of_mem_idealOfVars hx
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl f)

def mvEvalAdic (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) [IsAdicComplete J S]
    (x : σ → S) (hx : ∀ i, x i ∈ J) : MvPowerSeries σ A →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx)

theorem mvEvalAdic_sub_aeval_truncTotal_mem (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (n : ℕ) (f : MvPowerSeries σ A) :
    mvEvalAdic A J x hx f - MvPolynomial.aeval x (truncTotal n f) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq]
  exact IsAdicComplete.mk_liftAlgHom J (mvEvalMod A J x hx) (factor_comp_mvEvalMod J x hx) n f

@[simp] theorem mvEvalAdic_coe (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (p : MvPolynomial σ A) :
    mvEvalAdic A J x hx p = MvPolynomial.aeval x p := by
  refine eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  have h1 := mvEvalAdic_sub_aeval_truncTotal_mem J x hx n (p : MvPowerSeries σ A)
  have h2 : MvPolynomial.aeval x (truncTotal n (p : MvPowerSeries σ A) - p) ∈ J ^ n := by
    refine aeval_mem_pow_of_mem_idealOfVars hx ?_
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hd, MvPolynomial.coeff_coe, sub_self]
  simpa using add_mem h1 h2

@[simp] theorem mvEvalAdic_X (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (i : σ) : mvEvalAdic A J x hx (X i) = x i := by
  simpa using mvEvalAdic_coe (A := A) J x hx (MvPolynomial.X i)

@[simp] theorem mvEvalAdic_C (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (a : A) : mvEvalAdic A J x hx (C a) = algebraMap A S a :=
  (mvEvalAdic A J x hx).commutes a

theorem algHom_mem_pow_of_le_order (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) {n : ℕ} {g : MvPowerSeries σ A} (hg : (n : ℕ∞) ≤ g.order) :
    φ g ∈ K ^ n := by
  have h : (germIdeal σ A).map φ ≤ K := by
    rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.mem_map_of_mem φ (mem_germIdeal_pow_iff_le_order.2 hg)
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono h n this

theorem algHom_sub_constantCoeff_mem (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) (g : MvPowerSeries σ A) :
    φ g - algebraMap A S (constantCoeff g) ∈ K := by
  have h : φ (g - C (constantCoeff g)) ∈ K ^ 1 :=
    algHom_mem_pow_of_le_order φ hφ (mem_germIdeal_pow_iff_le_order.1 (by simp [RingHom.mem_ker]))
  rw [pow_one, map_sub] at h
  rwa [← φ.commutes]

omit [Finite σ] in
theorem algHom_coe_mvPolynomial (φ : MvPowerSeries σ A →ₐ[A] S) (p : MvPolynomial σ A) :
    φ p = MvPolynomial.aeval (fun i => φ (X i)) p := by
  have : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom A) =
      MvPolynomial.aeval (fun i => φ (X i)) := by
    ext; simp
  simpa using DFunLike.congr_fun this p

theorem algHom_sub_aeval_truncTotal_mem (φ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (n : ℕ) (g : MvPowerSeries σ A) :
    φ g - MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) ∈ J ^ n := by
  rw [← algHom_coe_mvPolynomial, ← map_sub]
  refine algHom_mem_pow_of_le_order φ hφ (nat_le_order fun d hd => ?_)
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]

theorem algHom_sub_mem_pow (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (hψ : ∀ i, ψ (X i) ∈ J) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ J ^ n) (g : MvPowerSeries σ A) : φ g - ψ g ∈ J ^ n := by
  have h1 := algHom_sub_aeval_truncTotal_mem φ hφ n g
  have h2 := algHom_sub_aeval_truncTotal_mem ψ hψ n g
  have h3 : MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) -
      MvPolynomial.aeval (fun i => ψ (X i)) (truncTotal n g) ∈ J ^ n := by
    have : (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => φ (X i))) =
        (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => ψ (X i))) := by
      ext i
      simpa [Ideal.Quotient.eq] using h i
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun this _
  have := sub_mem (add_mem h1 h3) h2
  convert this using 1
  ring

theorem mvPowerSeries_algHom_ext_of_isHausdorff (J : Ideal S) [IsHausdorff J S]
    {φ ψ : MvPowerSeries σ A →ₐ[A] S} (hφ : ∀ i, φ (X i) ∈ J) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ :=
  AlgHom.ext fun g => eq_of_forall_sub_mem_ideal_pow J fun n =>
    algHom_sub_mem_pow φ ψ hφ (fun i => h i ▸ hφ i) (fun i => by simp [h i]) g

end Eval

end GlobalTheory
