import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.Energy
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProdProofB
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical MeasureTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Mean4O.InhabCalc

section Analysis

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem mInt_congr_φ (A : FinHolAtlas e X) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  unfold mInt integralWith locDens
  simp only [h]

theorem mInt_update_add' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e)
    (P Q : LocPot X) (hF : ∀ i, IsPotential A (F i)) (hP : IsPotential A P) (hQ : IsPotential A Q) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update F k (P + Q)) g = mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g := by
  cases e with
  | zero => exact k.elim0
  | succ e => convert ReciprocityTheory.AnForm.P.mInt_update_add A F k P Q hF hP hQ g hg

theorem mInt_update_rsmul (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e) (c : ℝ)
    (P : LocPot X) (hF : ∀ i, IsPotential A (F i)) (hP : IsPotential A P) (g : X → ℝ) :
    mInt A (Function.update F k (P.rsmul c)) g = c * mInt A (Function.update F k P) g := by
  cases e with
  | zero => exact k.elim0
  | succ e =>
    have h := mIntRsmul A c P (Fin.tail (F ∘ Equiv.swap 0 k)) hP (fun i => hF _) g
    rw [← ReciprocityTheory.AnForm.P.mInt_update_eq, ← ReciprocityTheory.AnForm.P.mInt_update_eq] at h
    convert h

def combPot {I : Type} [Fintype I] (P : I → LocPot X) (a : I → ℝ) (u : X → ℝ) : LocPot X where
  U x := ⋂ i, (P i).U x
  isOpen_U x := isOpen_iInter_of_finite fun i => (P i).isOpen_U x
  mem_U x := Set.mem_iInter.2 fun i => (P i).mem_U x
  φ x y := ∑ i, a i * (P i).φ x y + u y

theorem isPotential_combPot (A : FinHolAtlas e X) {I : Type} [Fintype I] (P : I → LocPot X)
    (hP : ∀ i, IsPotential A (P i)) (a : I → ℝ) (u : X → ℝ) (hu : A.Smooth u) : IsPotential A (combPot P a u) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have h1 : ∀ i, ContDiffOn ℝ ∞ (fun y => a i * (P i).φ x ((A.chart j).symm y))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (combPot P a u).U x) := fun i =>
      contDiffOn_const.mul (((hP i).1 x j).mono
        (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ i))))
    exact (ContDiffOn.sum fun i _ => h1 i).add
      ((hu j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ _))))
  · choose W hW hyW G hG hφ using fun i =>
      (hP i).2 x x' y ⟨Set.mem_iInter.1 hy.1 i, Set.mem_iInter.1 hy.2 i⟩
    refine ⟨⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hyW, fun z => ∑ i, (a i : ℂ) * G i z, fun j => ?_, ?_⟩
    · intro t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · rintro z ⟨⟨h0, h1⟩, h2⟩
      simp only [combPot, Complex.re_sum, Complex.re_ofReal_mul]
      rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hφ i z ⟨⟨Set.mem_iInter.1 h0 i, Set.mem_iInter.1 h1 i⟩, Set.mem_iInter.1 h2 i⟩, mul_sub]

end Analysis

section Calculus

variable {e : ℕ} (M : Man e)

def smSub : Submodule ℝ M.Fun where
  carrier := {u | M.Smooth u}
  add_mem' hu hv σ j := (hu σ j).add (hv σ j)
  zero_mem' _ _ := contDiffOn_const
  smul_mem' c _ hu σ j := (contDiffOn_const (c := c)).mul (hu σ j)

variable {I : Type} [Fintype I] (P : I → M.Pot)

def chern (v : (I → ℝ) × smSub M) : M.Pot := fun σ => combPot (fun i => P i σ) v.1 ((v.2 : M.Fun) σ)

theorem chern_add_φ (v w : (I → ℝ) × smSub M) (σ) :
    (chern M P (v + w) σ).φ = (chern M P v σ + chern M P w σ).φ := by
  funext x y
  simp only [add_φ, chern, combPot, Prod.fst_add, Prod.snd_add, Pi.add_apply, Submodule.coe_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem chern_smul_φ (c : ℝ) (v : (I → ℝ) × smSub M) (σ) :
    (chern M P (c • v) σ).φ = ((chern M P v σ).rsmul c).φ := by
  funext x y
  simp only [LocPot.rsmul, chern, combPot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul,
    smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

theorem mInt_chern_update (v : Fin e → (I → ℝ) × smSub M) (k : Fin e) (x : (I → ℝ) × smSub M) (σ)
    (R : LocPot (M.X σ)) (hR : (chern M P x σ).φ = R.φ) (g : M.X σ → ℝ) :
    mInt (M.A σ) (fun i => chern M P (Function.update v k x i) σ) g =
      mInt (M.A σ) (Function.update (fun i => chern M P (v i) σ) k R) g := by
  refine mInt_congr_φ _ (fun i => ?_) g
  by_cases h : i = k
  · subst h
    simpa using hR
  · simp [Function.update_of_ne h]

variable (hP : ∀ i σ, IsPotential (M.A σ) (P i σ))

include hP in
theorem chern_pot (v : (I → ℝ) × smSub M) (σ) : IsPotential (M.A σ) (chern M P v σ) :=
  isPotential_combPot _ _ (fun i => hP i σ) _ _ (v.2.2 σ)

def intML (u : smSub M) : MultilinearMap ℝ (fun _ : Fin e => (I → ℝ) × smSub M) ℝ :=
  MultilinearMap.mk' (fun v => M.int (fun i => chern M P (v i)) u)
    (fun v k x y => by
      simp only [Man.int]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mInt_chern_update M P v k _ σ _ (chern_add_φ M P x y σ), mInt_chern_update M P v k x σ _ rfl,
        mInt_chern_update M P v k y σ _ rfl]
      exact mInt_update_add' _ _ k _ _ (fun i => chern_pot M P hP _ σ) (chern_pot M P hP _ σ) (chern_pot M P hP _ σ) _
        (projLine_continuous_of_smooth _ (u.2 σ)))
    (fun v k c x => by
      simp only [Man.int, smul_eq_mul]
      rw [mul_left_comm, Finset.mul_sum _ _ c]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mInt_chern_update M P v k _ σ _ (chern_smul_φ M P c x σ), mInt_chern_update M P v k x σ _ rfl]
      exact mInt_update_rsmul _ _ k _ _ (fun i => chern_pot M P hP _ σ) (chern_pot M P hP _ σ) _)

theorem intML_apply (u : smSub M) (v : Fin e → (I → ℝ) × smSub M) :
    intML M P hP u v = M.int (fun i => chern M P (v i)) u := rfl

theorem intML_lin (c : ℝ) (u u' : smSub M) (v : Fin e → (I → ℝ) × smSub M) :
    intML M P hP (c • u + u') v = c * intML M P hP u v + intML M P hP u' v := by
  simp only [intML_apply, Man.int]
  rw [mul_left_comm, Finset.mul_sum _ _ c, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ i, IsPotential (M.A σ) (chern M P (v i) σ) := fun i => chern_pot M P hP _ σ
  exact mIntLinear _ _ hc c _ _ (mIntegrableCont _ _ hc _ (projLine_continuous_of_smooth _ (u.2 σ)))
    (mIntegrableCont _ _ hc _ (projLine_continuous_of_smooth _ (u'.2 σ)))

def intL : smSub M →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin e => (I → ℝ) × smSub M) ℝ where
  toFun := intML M P hP
  map_add' u u' := by
    ext v
    simpa using intML_lin M P hP 1 u u' v
  map_smul' c u := by
    ext v
    have h0 := intML_lin M P hP 1 0 0 v
    have h1 := intML_lin M P hP c u 0 v
    simp only [smul_zero, add_zero, one_mul, left_eq_add] at h0 h1
    simp [h1, h0]

def form0 : MultilinearMap ℝ (fun _ : Fin (e + 1) => (I → ℝ) × smSub M) ℝ :=
  LinearMap.uncurryLeft (M := fun _ : Fin (e + 1) => (I → ℝ) × smSub M) ((intL M P hP).comp (LinearMap.snd ℝ _ _))

end Calculus

end GlobalTheory.Mean4O.InhabCalc
