import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count.Test

open Formalism.MainNotions.S GlobalTheory.Count

variable (I : AutInst)

theorem mem_lamX (x : I.GA) (y : Fin I.n → I.E) : y ∈ lamX I x ↔
    I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
  constructor
  · intro hy
    unfold lamX at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      have e0 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        ext i; simp
      rw [e0, Matrix.mulVec_zero]
      exact zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ =>
      have e2 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z₁ + z₂) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₁ i)) +
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₂ i)) := by
        ext i; simp
      rw [e2, Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul a z _ hz =>
      have hc : Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) ∈ IntAf I.F I.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((a • z) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) •
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z i)) := by
        ext i; simp [Algebra.smul_def]
      rw [e1, Matrix.mulVec_smul]
      exact I.Lf.smul_mem ⟨_, hc⟩ hz
  · intro hy
    exact Submodule.subset_span hy

theorem le_lamX_one : I.L ≤ lamX I 1 := by
  intro y hy
  rw [mem_lamX]
  have h1 : I.fmat (1 : I.GA).2⁻¹ = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem one_mem_GF : (1 : I.GA) ∈ I.GFset := by
  simp only [AutInst.GFset, Set.mem_ofPred_eq]
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hdet]
  · simp [AutInst.fmat]

theorem lamX_equivariant (g x : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (y : Fin I.n → I.E) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (g * x) ↔ y ∈ lamX I x := by
  have hm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by
    simp [AutInst.fmat]
  have h1 : I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hinc : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
      (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat g.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    ext i
    rw [h, RingHom.map_mulVec]
    rfl
  rw [mem_lamX, mem_lamX, hinc, Prod.snd_mul, _root_.mul_inv_rev, hm, Matrix.mulVec_mulVec, mul_assoc,
    ← hm g.2⁻¹ g.2, inv_mul_cancel, h1, mul_one]

theorem embedding_cases (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm.cmUnram.2.1
  have hF : ∀ a : I.F, w.embedding (algebraMap I.F I.E a) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E a) := by
    have := I.cm.totReal
    have hv : w.comap (algebraMap I.F I.E) =
        InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    have hψ : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := RingHom.ext (I.φ_over _)
    have hreal : ComplexEmbedding.conjugate (w.embedding.comp (algebraMap I.F I.E)) =
        w.embedding.comp (algebraMap I.F I.E) :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _))
    have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) =
        InfinitePlace.mk ((I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E)) := by
      rw [hψ, InfinitePlace.mk_embedding, hv]
    have key : w.embedding.comp (algebraMap I.F I.E) =
        (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) := by
      rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
      · exact h
      · rwa [hreal] at h
    intro a
    exact RingHom.congr_fun key a
  set ψ := I.φ (w.comap (algebraMap I.F I.E)) with hψdef
  have hpt : ∀ e : I.E, w.embedding e = ψ e ∨ w.embedding e = starRingEnd ℂ (ψ e) := by
    intro e
    obtain ⟨s, hs⟩ := (I.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨t, ht⟩ := (I.cm.fixed (e * star e)).1 (by rw [star_mul, star_star])
    have h1 : w.embedding e + starRingEnd ℂ (w.embedding e) = ψ e + starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_add, ← map_add, ← hs, hF]
    have h2 : w.embedding e * starRingEnd ℂ (w.embedding e) = ψ e * starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_mul, ← map_mul, ← ht, hF]
    have h3 : (w.embedding e - ψ e) * (w.embedding e - starRingEnd ℂ (ψ e)) = 0 := by
      linear_combination (w.embedding e) * h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a, w.embedding a ≠ ψ a := by
    by_contra hc
    push Not at hc
    exact hne1 (RingHom.ext hc)
  obtain ⟨b, hb⟩ : ∃ b, w.embedding b ≠ starRingEnd ℂ (ψ b) := by
    by_contra hc
    push Not at hc
    exact hne2 (RingHom.ext fun x => (hc x).trans (ComplexEmbedding.conjugate_coe_eq ψ x).symm)
  have ha' := (hpt a).resolve_left ha
  have hb' := (hpt b).resolve_right hb
  rcases hpt (a + b) with h | h
  · apply ha
    rw [map_add, map_add] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add, map_add, map_add] at h
    linear_combination h - ha'

theorem frm_frame (x : I.GA) (w : InfinitePlace I.E) :
    (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
  have hU : (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ * Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) *
      uMat (x.1 (w.comap (algebraMap I.F I.E))) = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) :=
    (x.1 (w.comap (algebraMap I.F I.E))).2
  have key : (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
      I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) =
      Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
          ((I.P (w.comap (algebraMap I.F I.E)))ᴴ * I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
            I.P (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [I.P_spec]; exact hU
  have hc : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    intro A; ext i j; simp [Matrix.conjTranspose_apply]
  simp only [frm]
  split_ifs with h
  · rw [h]; exact key
  · rw [(embedding_cases I w).resolve_left h]
    have hJ : I.J.map (ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E)))) =
        (I.J.map (I.φ (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hJ, hc, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem one_mem_nearSet (x : I.GA) {δ : ℝ} (hδ : 0 ≤ δ) : (1 : I.GA) ∈ nearSet I x δ := by
  simp only [nearSet, Set.mem_ofPred_eq]
  refine ⟨one_mem_GF I, ?_, fun v => ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact one_mem (Formalism.UG.stabGL I.Lf)
  · simp [uMat, Formalism.REAL.hs, hδ]

end GlobalTheory.Count.Test
