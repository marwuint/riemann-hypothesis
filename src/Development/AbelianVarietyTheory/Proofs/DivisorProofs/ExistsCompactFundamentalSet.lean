import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.SWLit.WittStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

variable (σ : E →ₐ[F] E) {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)

theorem incM_inv_mul : incM F (T⁻¹).1 * incM F T.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]

theorem incM_mul_inv : incM F T.1 * incM F (T⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]

theorem inBasis_mul (g h : UA σ J₂) : inBasis σ T (g * h) = inBasis σ T g * inBasis σ T h := by
  simp only [inBasis]
  rw [show mat (g * h) = mat g * mat h from rfl]
  calc incM F (T⁻¹).1 * (mat g * mat h) * incM F T.1
      = incM F (T⁻¹).1 * mat g * (incM F T.1 * incM F (T⁻¹).1) * mat h * incM F T.1 := by
        rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inBasis_one : inBasis σ T (1 : UA σ J₂) = 1 := by
  simp only [inBasis]
  rw [show mat (1 : UA σ J₂) = 1 from rfl, Matrix.mul_one, incM_inv_mul]

theorem entry_mul_mem (v : HeightOneSpectrum (𝓞 F)) {A B : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)}
    (hA : ∀ i j, compFin F E v (A i j) ∈ intLoc F E v) (hB : ∀ i j, compFin F E v (B i j) ∈ intLoc F E v) (i j) :
    compFin F E v ((A * B) i j) ∈ intLoc F E v := by
  rw [Matrix.mul_apply, map_sum]
  exact Subring.sum_mem _ fun k _ => by rw [map_mul]; exact Subring.mul_mem _ (hA i k) (hB k j)

def stdK : Subgroup (UA σ J₂) where
  carrier := {g | (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧
      compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ}
  one_mem' := by
    refine ⟨fun v i j => ?_, fun w τ => ?_⟩
    · rw [inv_one, inBasis_one, Matrix.one_apply]
      split_ifs <;> simp [one_mem, zero_mem]
    · rw [inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
  mul_mem' := by
    intro g h hg hh
    refine ⟨fun v i j => ⟨?_, ?_⟩, fun w τ => ?_⟩
    · rw [inBasis_mul]
      exact entry_mul_mem v (fun i j => (hg.1 v i j).1) (fun i j => (hh.1 v i j).1) i j
    · rw [mul_inv_rev, inBasis_mul]
      exact entry_mul_mem v (fun i j => (hh.1 v i j).2) (fun i j => (hg.1 v i j).2) i j
    · rw [inBasis_mul, Matrix.map_mul]
      exact mul_mem (hg.2 w τ) (hh.2 w τ)
  inv_mem' := by
    intro g hg
    refine ⟨fun v i j => ⟨(hg.1 v i j).2, by rw [inv_inv]; exact (hg.1 v i j).1⟩, fun w τ => ?_⟩
    have hU := hg.2 w τ
    set U := (inBasis σ T g).map (piInf τ)
    set V := (inBasis σ T g⁻¹).map (piInf τ)
    have hVU : V * U = 1 := by
      simp only [V, U]
      rw [← Matrix.map_mul, ← inBasis_mul, inv_mul_cancel, inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hV : V = star U := by
      calc V = V * (U * star U) := by rw [Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one]
        _ = (V * U) * star U := by rw [Matrix.mul_assoc]
        _ = star U := by rw [hVU, Matrix.one_mul]
    show V ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ
    rw [hV, Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.1 hU

omit [NumberField F] [NumberField E] in
theorem bc_val {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (f : A →+* B)
    (x : GL m A) : ((Formalism.UG.bc f x : GL m B) : Matrix m m B) = (x : Matrix m m A).map f := rfl

theorem piInf_eq {w : InfinitePlace F} (τ : EmbOver E w) : ⇑(piInf τ) = ⇑(infEmb τ) ∘ ⇑(compInf F E w) := rfl

end GlobalTheory.SWLit.WittStd

end
