import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceBwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colGroup_of_embX {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J) : g ∈ colGroup k κ (Fin τ) := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (s + 1)).range ≤ R k _ (s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact hg

theorem entries_of_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : g ∈ colGroup k κ (Fin τ)) (a b : XIx (Fin κ) (Fin τ) 0) :
    g.val a b ∈ 𝒪[k] ∧ (e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  obtain ⟨_, ⟨g₀, rfl, rfl⟩, hu⟩ := hg
  refine ⟨(g₀.val a b).2, fun hab => ?_⟩
  have h1 : residue 𝒪[k] (g₀.val a b) = (1 : Matrix _ _ 𝓀[k]) a b := hu a b (by rw [hp, hp]; exact hab)
  have h2 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
    simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
  rw [h2, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
  have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h1
  convert h3 using 2
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_mat {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k V.rank Y) (e : Y ≃ Fin V.rank) (hβ : F.β = (1 : Matrix (Fin V.rank) (Fin V.rank) k).submatrix id e) (x : GA D V) :
    ∃ g : GL Y k, (mt V x).map q.pr = F.β * g.val * F.γ ∧ ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := by
  have hmul : ∀ y z : GA D V, y * z = 1 → (F.γ * (mt V y).map q.pr * F.β) * (F.γ * (mt V z).map q.pr * F.β) = 1 := fun y z h => by
    have h1 : mt V y * mt V z = 1 := by
      have h2 : mt V y * mt V z = mt V (y * z) := rfl
      rw [h2, h]
      rfl
    have h3 : (mt V y).map q.pr * (mt V z).map q.pr = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = F.γ * ((mt V y).map q.pr * (F.β * F.γ) * (mt V z).map q.pr) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h3, Matrix.mul_one, F.γβ]
  let g : GL Y k := ⟨_, _, hmul x x⁻¹ (mul_inv_cancel x), hmul x⁻¹ x (inv_mul_cancel x)⟩
  have hg : (mt V x).map q.pr = F.β * g.val * F.γ := by
    calc _ = (F.β * F.γ) * (mt V x).map q.pr * (F.β * F.γ) := by rw [F.βγ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [g, Matrix.mul_assoc]
  refine ⟨g, hg, fun a b => ?_⟩
  have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [hβ] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm

end Loc

end GlobalTheory.FamTrace.TraceBwd

end
