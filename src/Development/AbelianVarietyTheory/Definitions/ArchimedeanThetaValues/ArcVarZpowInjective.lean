import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open Matrix in
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
  [Module.Finite ℤ X] in
private lemma exists_pos_nat_mul_eq_int {Idx : Type} [Fintype Idx] (q : Idx → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ w : Idx → ℤ, ∀ i, (w i : ℚ) = N * q i := by
  classical
  refine ⟨∏ i, (q i).den, Finset.prod_pos fun i _ => (q i).pos,
    fun i => (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ), fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)]
  push_cast
  rw [← Rat.mul_den_eq_num (q i)]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open Matrix in
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
  [Module.Finite ℤ X] in

theorem _root_.GlobalTheory.ToricData.finite_form_le (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (hp : ∀ y, y ≠ 0 → 0 < be y y) (C : ℤ) : {y | be y y ≤ C}.Finite := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  set Idx := Module.Free.ChooseBasisIndex ℤ X
  let A : Matrix Idx Idx ℤ := fun i j => be (b i) (b j)
  have hQ : ∀ y, be y y = b.repr y ⬝ᵥ A *ᵥ b.repr y := by
    intro y
    have h := congrArg (fun B : LinearMap.BilinForm ℤ X => B y y) (Matrix.toBilin_toMatrix b be)
    simp only [Matrix.toBilin_apply, LinearMap.BilinForm.toMatrix_apply] at h
    rw [← h]
    simp only [A, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpos : ∀ w : Idx → ℤ, w ≠ 0 → 0 < w ⬝ᵥ A *ᵥ w := by
    intro w hw
    have h := hp (b.equivFun.symm w) (b.equivFun.symm.map_ne_zero_iff.mpr hw)
    rwa [hQ, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at h
  let AR : Matrix Idx Idx ℝ := A.map (Int.cast : ℤ → ℝ)
  have hcastR : ∀ w : Idx → ℤ, (fun i => (w i : ℝ)) ⬝ᵥ AR *ᵥ (fun i => (w i : ℝ)) =
      ((w ⬝ᵥ A *ᵥ w : ℤ) : ℝ) := by
    intro w
    simp [AR, dotProduct, Matrix.mulVec]
  have hnn : ∀ v : Idx → ℝ, 0 ≤ v ⬝ᵥ AR *ᵥ v := by
    intro v
    have hd : DenseRange (Pi.map fun _ : Idx => (Rat.cast : ℚ → ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun v => 0 ≤ v ⬝ᵥ AR *ᵥ v) v
      (isClosed_le continuous_const (by fun_prop)) fun q => ?_
    obtain ⟨N, hN, w, hw⟩ := exists_pos_nat_mul_eq_int q
    have hwv : (fun i => (w i : ℝ)) =
        (N : ℝ) • Pi.map (fun _ : Idx => (Rat.cast : ℚ → ℝ)) q := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hw i)
      push_cast at this
      simpa using this
    have h1 : 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ AR *ᵥ (fun i => (w i : ℝ)) := by
      rw [hcastR]
      by_cases hw0 : w = 0
      · simp [hw0]
      · exact_mod_cast (hpos w hw0).le
    rw [hwv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact (mul_nonneg_iff_of_pos_left hN').mp ((mul_nonneg_iff_of_pos_left hN').mp h1)
  have hdetA : A.det ≠ 0 := by
    intro h0
    let AQ : Matrix Idx Idx ℚ := A.map (Int.cast : ℤ → ℚ)
    have hQdet : AQ.det = 0 := by
      have h2 : ((A.det : ℤ) : ℚ) = AQ.det := (Int.castRingHom ℚ).map_det A
      rw [← h2, h0, Int.cast_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hQdet
    obtain ⟨N, hN, w, hw⟩ := exists_pos_nat_mul_eq_int v
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hw0 : w ≠ 0 := by
      intro hw0
      apply hv0
      funext i
      have h := hw i
      simp only [hw0, Pi.zero_apply, Int.cast_zero] at h
      simpa using (mul_eq_zero.mp h.symm).resolve_left hN0
    have hwv : (fun i => (w i : ℚ)) = (N : ℚ) • v := funext fun i => by simp [hw i]
    have hzero : ((w ⬝ᵥ A *ᵥ w : ℤ) : ℚ) = 0 := by
      have h3 : ((w ⬝ᵥ A *ᵥ w : ℤ) : ℚ) =
          (fun i => (w i : ℚ)) ⬝ᵥ AQ *ᵥ (fun i => (w i : ℚ)) := by
        simp [AQ, dotProduct, Matrix.mulVec]
      rw [h3, hwv, Matrix.mulVec_smul, hv]
      simp
    have h4 := hpos w hw0
    have h5 : (w ⬝ᵥ A *ᵥ w) = 0 := by exact_mod_cast hzero
    omega
  have hherm : AR.IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    show ((be (b j) (b i) : ℤ) : ℝ) = ((be (b i) (b j) : ℤ) : ℝ)
    rw [hs]
  have hpsd : AR.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => by simpa using hnn x
  have hdetR : AR.det ≠ 0 := by
    have h2 : ((A.det : ℤ) : ℝ) = AR.det := (Int.castRingHom ℝ).map_det A
    rw [← h2]
    exact_mod_cast hdetA
  have hpd : AR.PosDef := hpsd.posDef_iff_det_ne_zero.mpr hdetR
  have hposR : ∀ v : Idx → ℝ, v ≠ 0 → 0 < v ⬝ᵥ AR *ᵥ v := fun v hv => by
    simpa using hpd.dotProduct_mulVec_pos hv
  have hcont : Continuous fun v : Idx → ℝ => v ⬝ᵥ AR *ᵥ v := by fun_prop
  obtain ⟨m, hm, hmv⟩ : ∃ m : ℝ, 0 < m ∧ ∀ v : Idx → ℝ, m * ‖v‖ ^ 2 ≤ v ⬝ᵥ AR *ᵥ v := by
    by_cases hS : (Metric.sphere (0 : Idx → ℝ) 1).Nonempty
    · obtain ⟨v0, hv0, hmin⟩ :=
        (isCompact_sphere (0 : Idx → ℝ) 1).exists_isMinOn hS hcont.continuousOn
      have hv0' : v0 ≠ 0 := by rintro rfl; simp at hv0
      refine ⟨_, hposR v0 hv0', fun v => ?_⟩
      by_cases hv : v = 0
      · simp [hv]
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Idx → ℝ) 1 := by
        simp [norm_smul, hnv.ne']
      have h1 := isMinOn_iff.mp hmin _ hu
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
      calc v0 ⬝ᵥ AR *ᵥ v0 * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ AR *ᵥ v))) * ‖v‖ ^ 2 := by
            gcongr
        _ = v ⬝ᵥ AR *ᵥ v := by field_simp
    · refine ⟨1, one_pos, fun v => ?_⟩
      have hv : v = 0 := by
        by_contra hv
        exact hS ⟨‖v‖⁻¹ • v, by simp [norm_smul, (norm_pos_iff.mpr hv).ne']⟩
      simp [hv]
  set R : ℕ := ⌈(C : ℝ) / m⌉₊ + 1 with hR
  have hbound : ∀ c : Idx → ℤ, c ⬝ᵥ A *ᵥ c ≤ C → ∀ i, |c i| ≤ R := by
    intro c hc i
    have h1 : m * ‖(fun j => (c j : ℝ))‖ ^ 2 ≤ C := by
      have h0 := hmv (fun j => (c j : ℝ))
      rw [hcastR c] at h0
      exact h0.trans (by exact_mod_cast hc)
    have h2 : |(c i : ℝ)| ≤ ‖(fun j => (c j : ℝ))‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => (c j : ℝ)) i
    have h6 := Nat.le_ceil ((C : ℝ) / m)
    have h7 : (0 : ℝ) ≤ ⌈(C : ℝ) / m⌉₊ := Nat.cast_nonneg _
    have h3 : (|c i| : ℝ) ≤ R := by
      rw [hR]
      push_cast
      rcases le_or_gt |(c i : ℝ)| 1 with h | h
      · linarith
      · have h4 : |(c i : ℝ)| ≤ ‖(fun j => (c j : ℝ))‖ ^ 2 := by nlinarith
        have h5 : ‖(fun j => (c j : ℝ))‖ ^ 2 ≤ (C : ℝ) / m := by
          rw [le_div_iff₀ hm]
          linarith
        linarith
    exact_mod_cast h3
  have hT : (Set.pi Set.univ fun _ : Idx => Set.Icc (-(R : ℤ)) R).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hT.image b.equivFun.symm).subset fun y hy => ?_
  refine ⟨b.equivFun y, fun i _ => ?_, b.equivFun.symm_apply_apply y⟩
  have h := hbound (b.equivFun y) (by rw [Module.Basis.equivFun_apply, ← hQ]; exact hy) i
  exact abs_le.mp h

section ThetaShiftProofs

def arcVar (k : Type) [Field k] : (FractionRing (PowerSeries k))ˣ :=
  Units.mk0 (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero)

def arcExp (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X) (y : X) : (FractionRing (PowerSeries k))ˣ :=
  Units.mk0 (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero) ^ (be y y / 2)

variable (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X)

theorem arcVar_val :
    (arcVar k : FractionRing (PowerSeries k)) = algebraMap (PowerSeries k) _ PowerSeries.X := rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_eq (y : X) : arcExp k be y = arcVar k ^ (be y y / 2) := rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_val (y : X) : (arcExp k be y : FractionRing (PowerSeries k)) =
    algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) PowerSeries.X ^ (be y y / 2) :=
  Units.val_zpow_eq_zpow_val _ _

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem arcExp_neg (y : X) : arcExp k be (-y) = arcExp k be y := by
  simp only [arcExp_eq, map_neg, LinearMap.neg_apply, neg_neg]

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem polar_arcExp (hs : ∀ y z, be y z = be z y) (he : ∀ y, (2 : ℤ) ∣ be y y) (y z : X) :
    polar (arcExp k be) y z = arcVar k ^ (be y z) := by
  rw [polar, arcExp_eq, arcExp_eq, arcExp_eq, ← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add]
  congr 1
  have h1 := he y
  have h2 := he z
  simp only [map_add, LinearMap.add_apply, hs z y]
  omega

theorem psiIn_arcExp_iff (y : X) (n : ℕ) :
    (toricPre _ X (arcExp k be)).PsiIn y (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ n) ↔
      (n : ℤ) ≤ be y y / 2 := by
  rw [psiIn_iff, Ideal.span_singleton_pow]
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.1 hr
    by_contra hlt
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) = be y y / 2 + (m + 1 : ℕ) := ⟨((n : ℤ) - be y y / 2 - 1).toNat, by omega⟩
    have hX := (arcVar k).ne_zero
    rw [arcVar_val] at hX
    have h1 : (PowerSeries.X : PowerSeries k) ^ (m + 1) * s = 1 :=
      IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k)) (by
        rw [arcExp_val, map_mul, map_pow, ← zpow_natCast, hm, zpow_add₀ hX, _root_.mul_assoc, zpow_natCast] at h
        rw [map_mul, map_pow, map_one]
        exact (mul_left_cancel₀ (zpow_ne_zero _ hX) ((_root_.mul_one _).trans h)).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp at h2
  · intro h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, be y y / 2 = (n + m : ℕ) := ⟨(be y y / 2 - n).toNat, by omega⟩
    refine ⟨PowerSeries.X ^ (n + m), Ideal.mem_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right _ _)), ?_⟩
    rw [arcExp_val, hm, zpow_natCast, map_pow]

def arcData (k : Type) [Field k] (be : LinearMap.BilinForm ℤ X) (hs : ∀ y z, be y z = be z y)
    (hp : ∀ y, y ≠ 0 → 0 < be y y) (he : ∀ y, (2 : ℤ) ∣ be y y) :
    DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) where
  toPre := toricPre _ X (arcExp k be)
  psi_even := psiEven _ (arcExp_neg k be)
  tau_bimult := tauBimult _ fun a a' b => by
    rw [polar_arcExp k be hs he, polar_arcExp k be hs he, polar_arcExp k be hs he, map_add, LinearMap.add_apply,
      zpow_add]
  psi_pos := fun (y : X) hy => by
    have h1 := hp y hy
    have h2 := he y
    have := (psiIn_arcExp_iff k be y 1).2 (by omega)
    rwa [pow_one] at this
  psi_tendsto := fun n => (finite_form_le be hs hp (2 * n)).subset fun (y : X) hy => by
    have : ¬ (n : ℤ) ≤ be y y / 2 := fun h => hy ((psiIn_arcExp_iff k be y n).2 h)
    change be y y ≤ 2 * n
    omega

variable (hs : ∀ y z, be y z = be z y) (hp : ∀ y, y ≠ 0 → 0 < be y y) (he : ∀ y, (2 : ℤ) ∣ be y y)

instance (O : Type) [Ring O] [Module O X] : Module O (arcData k be hs hp he).toPre.X :=
  inferInstanceAs (Module O X)

end ThetaShiftProofs

section Examples

def twoMul : LinearMap.BilinForm ℤ ℤ := (2 : ℤ) • LinearMap.mul ℤ ℤ

end Examples

end GlobalTheory.ToricData
