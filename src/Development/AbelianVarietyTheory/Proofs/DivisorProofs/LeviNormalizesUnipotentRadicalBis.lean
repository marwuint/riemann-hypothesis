import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

end GlobalTheory.ResLine.LeviFacts
