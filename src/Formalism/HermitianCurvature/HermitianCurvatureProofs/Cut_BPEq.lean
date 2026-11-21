import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem ttp_eq (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold Formalism.FourierDecayAlt.TBB.TTp
  rw [hz, hz']
  rfl

theorem isBoundedBilinearMap_compSh :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq' →L[ℂ] Wq) => q.1.comp q.2) where
  add_left x₁ x₂ y := ContinuousLinearMap.add_comp x₁ x₂ y
  smul_left c x y := by ext v; simp
  add_right x y₁ y₂ := ContinuousLinearMap.comp_add x y₁ y₂
  smul_right c x y := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
    exact ContinuousLinearMap.map_smul_of_tower x c (y v)
  bound := ⟨1, one_pos, fun x y => by simpa using ContinuousLinearMap.opNorm_comp_le x y⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_compSh {k r : ℕ} {f : B.Mat k r → (Wq →L[ℂ] Wp)} {A : B.Mat k r → (Wq' →L[ℂ] Wq)}
    (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (f2 g), hU1.inter hU2, ⟨hg1, hg2⟩, ?_,
    fun g hg hgv => by
      show (f g).comp (A g) = (f1 g).comp (f2 g)
      rw [he1 g hg.1 hgv, he2 g hg.2 hgv]⟩
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g)) (U1 ∩ U2) := by
    first
    | exact (hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right)
    | exact (hc1.mono Set.inter_subset_left).prod (hc2.mono Set.inter_subset_right)
  exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn hp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_fpmSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hA : B.CkOn ⊤ (B.GV P.k P.r) A) : B.CkOn ⊤ (B.GV P.k P.r) (fpmSh q f A p₀) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf q.T.base.z q.T.base.z').pow p₀)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc (ckOn_compSh hf hA)

end sh

def PolyOp {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (d : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → B.Mat k r → ℂ) (L : Fin n → (Wq' →L[ℂ] Wq)),
    (∀ i, U.IsPolyDeg d (c i)) ∧ ∀ g, A g = ∑ i, c i g • L i

def FpmShDecay : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ) (d p₀ : ℕ),
    (∀ m : ℕ, B.InCC A₀ m f) → PolyOp d A →
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m (fpmSh q f A p₀)

end

end Formalism.FourierDecayAlt.P.CutBPEq
