import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SchurLin

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem sb_translate {f : V → ℂ} (hf : f ∈ SB V) (Z : V) : (fun Y => f (Y + Z)) ∈ SB V :=
  ⟨hf.1.comp_continuous (continuous_add_right Z), hf.2.comp_homeomorph (Homeomorph.addRight Z)⟩

theorem sb_indicator (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V)) :
    (U : Set V).indicator (1 : V → ℂ) ∈ SB V := by
  have hcl : IsClosed (U : Set V) := AddSubgroup.isClosed_of_isOpen U ho
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (U : Set V)
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  exact HasCompactSupport.intro' hc hcl (fun x hx => Set.indicator_of_notMem hx _)

theorem sb_eventually_invariant {f : V → ℂ} (hf : f ∈ SB V) :
    ∀ᶠ w in 𝓝 (0 : V), ∀ Y, f (Y + w) = f Y := by
  have h1 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + w) = f Y := by
    apply hf.2.isCompact.eventually_forall_of_forall_eventually
    intro Y _
    have hc : Tendsto (fun z : V × V => z.2 + z.1) (𝓝 ((0 : V), Y)) (𝓝 Y) := by
      have hcont : Continuous (fun z : V × V => z.2 + z.1) := by fun_prop
      convert hcont.tendsto ((0 : V), Y) using 2
      simp
    have hc2 : Tendsto (fun z : V × V => z.2) (𝓝 ((0 : V), Y)) (𝓝 Y) :=
      continuous_snd.tendsto _
    filter_upwards [hc.eventually (hf.1.eventually_eq Y), hc2.eventually (hf.1.eventually_eq Y)]
      with z h1 h2
    rw [h1, h2]
  have h2 : ∀ᶠ w in 𝓝 (0 : V), ∀ Y ∈ tsupport f, f (Y + -w) = f Y := by
    have : Tendsto (fun w : V => -w) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : V))
    exact this.eventually h1
  filter_upwards [h1, h2] with w hw1 hw2
  intro Y
  by_cases hY : Y ∈ tsupport f
  · exact hw1 Y hY
  by_cases hY' : Y + w ∈ tsupport f
  · have := hw2 _ hY'
    simp only [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']

variable (A : (V → ℂ) → V → ℂ)

end General

end GlobalTheory.SchurLin

namespace GlobalTheory.SchurLin

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def dualBall (ψ : AddChar K ℂ) (t : K) : AddSubgroup K where
  carrier := {y | ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1}
  zero_mem' := by
    intro o _
    simp
  add_mem' := by
    intro a b ha hb o ho
    simp only [Set.mem_setOf_eq] at *
    rw [mul_add, mul_add, AddChar.map_add_eq_mul, ha o ho, hb o ho, one_mul]
  neg_mem' := by
    intro a ha o ho
    have h : ψ (o * (t * a)) = 1 := ha o ho
    have h2 : ψ (o * (t * -a)) * ψ (o * (t * a)) = 1 := by
      rw [← AddChar.map_add_eq_mul, show o * (t * -a) + o * (t * a) = 0 by ring,
        AddChar.map_zero_eq_one]
    rw [h, mul_one] at h2
    exact h2

theorem mem_dualBall {ψ : AddChar K ℂ} {t y : K} :
    y ∈ dualBall ψ t ↔ ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1 := Iff.rfl

theorem dualBall_mem_nhds {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    (dualBall ψ t : Set K) ∈ 𝓝 0 := by
  have h := GlobalTheory.Published.SvN.eventually_psi hψc
  have ht : Tendsto (fun y : K => t * y) (𝓝 0) (𝓝 0) := by
    have := (continuous_mul_left t).tendsto (0 : K)
    rwa [mul_zero] at this
  filter_upwards [ht.eventually h] with y hy using hy

theorem dualBall_subset {ψ : AddChar K ℂ} {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {t : K} (ht : t ≠ 0) :
    (dualBall ψ t : Set K) ⊆ {y | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K (x₀ / t)} := by
  intro y hy
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_le] at hlt
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hlt
  have ho : x₀ / t / y ∈ (ValuativeRel.valuation K).integer := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ hlt.le zero_le'
  have := hy _ ho
  rw [show x₀ / t / y * (t * y) = x₀ by field_simp] at this
  exact hx₀ this

variable (n m : ℕ)

def latt (ψ : AddChar K ℂ) (t : K) : AddSubgroup (Matrix (Fin n) (Fin m) K) where
  carrier := {Y | ∀ i j, Y i j ∈ dualBall ψ t}
  zero_mem' := fun _ _ => (dualBall ψ t).zero_mem
  add_mem' := fun ha hb i j => (dualBall ψ t).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (dualBall ψ t).neg_mem (ha i j)

variable {n m}

theorem mem_latt {ψ : AddChar K ℂ} {t : K} {Y : Matrix (Fin n) (Fin m) K} :
    Y ∈ latt n m ψ t ↔ ∀ i j, Y i j ∈ dualBall ψ t := Iff.rfl

end Local

end GlobalTheory.SchurLin
