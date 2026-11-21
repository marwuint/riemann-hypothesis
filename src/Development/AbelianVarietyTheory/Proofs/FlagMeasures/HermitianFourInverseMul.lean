import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_int (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map L.cj

theorem hf_sum_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L H y (a i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_right, ih]

section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def proj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j
  map_add' a b := by
    simp only [hf_add_left, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c a := by
    simp only [hf_smul_left, mul_smul, RingHom.id_apply, smul_sub, Finset.smul_sum]

theorem proj_apply (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (v : S.V) : proj S g gs v =
    v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j := rfl

end General

theorem mem_stdLat (L : LocE F E) {n : ℕ} (x : Fin n → E) : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      show (Pi.single j 1 : Fin n → E) i ∈ L.O
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro i; exact zero_mem _
    | add u v _ _ hu hv => intro i; exact add_mem (hu i) (hv i)
    | smul c u _ hu =>
      intro i
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hu i)
  · intro hx
    have hsum : x = ∑ i, (⟨x i, hx i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSD_stdLat (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro v _
    have hsum : v = ∑ i, v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · intro y
    rw [mem_stdLat]
    constructor
    · intro h j
      have hrow : ∀ i, (Matrix.mulVec H fun k => L.cj (y k)) i ∈ L.O := by
        intro i
        have hs : (Pi.single i 1 : Fin n → E) ∈ stdLat L n := (mem_stdLat L _).2 fun k => by
          rw [Pi.single_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have := h _ hs
        simpa [hf, Pi.single_apply, Matrix.mulVec, dotProduct] using this
      have hcK : (fun k => L.cj (y k)) = Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k)) := by
        rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
      have hcj : (Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k))) j ∈ L.O := by
        simp only [Matrix.mulVec, dotProduct]
        exact Subring.sum_mem _ fun i _ => mul_mem (hK j i) (hrow i)
      rw [← hcK] at hcj
      have := cj_int L hcj
      simpa [L.cj_cj] using this
    · intro h x hx
      rw [mem_stdLat] at hx
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hx i) (hH i j)) (cj_int L (h j))

section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)

def big (H : Matrix (Fin s) (Fin s) E) : Matrix (Fin N) (Fin N) E :=
  Matrix.reindex e e (Matrix.fromBlocks H 0 0 (1 : Matrix (Fin m) (Fin m) E))

end Blocks

end GlobalTheory.HL.Inhab
