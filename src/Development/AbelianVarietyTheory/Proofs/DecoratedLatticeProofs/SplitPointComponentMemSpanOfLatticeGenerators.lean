import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.FullLatFrame

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : GlobalTheory.FinPl.SplitPt D k)

theorem e_int : finPart D q.e ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q]; exact (q.int_iff 1).1 (one_mem _)

theorem pr_int_mem (o : 𝓞 D.host.E) : q.pr (incA D (o : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨1, fun v => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem pr_pair_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) :
    q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE (e_int q) (AddSubgroup.subset_closure ⟨α, hα, 1, ?_⟩)
  rfl

variable {S : HSp D}

def aux₃ (x : Fin S.rank → D.host.E) : Fin S.rank → k := fun a => q.pr (incA D (x a))

theorem splitPointComponent_mem_span_of_lattice_generators {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    aux₃ q x ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  rw [← hG] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have h : aux₃ q (0 : Fin S.rank → D.host.E) = 0 := by funext a; simp [aux₃]
    rw [h]; exact zero_mem _
  | add x y _ _ hx hy =>
    have h : aux₃ q (x + y) = aux₃ q x + aux₃ q y := by funext a; simp [aux₃]
    rw [h]; exact add_mem hx hy
  | smul o x _ hx =>
    have h : aux₃ q (o • x) = (⟨_, pr_int_mem q o⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show q.pr (incA D (o • x a)) = q.pr (incA D (o : D.host.E)) * q.pr (incA D (x a))
      rw [Algebra.smul_def, map_mul, map_mul]
    rw [h]; exact Submodule.smul_mem _ _ hx

theorem pr_mem_span {L : GlobalTheory.FinPl.Lat S} (G : Finset (Fin S.rank → D.host.E))
    (hG : Submodule.span (𝓞 D.host.E) (G : Set (Fin S.rank → D.host.E)) = L) {y : Fin S.rank → AE D}
    (hy : y ∈ GlobalTheory.FinPl.latV S L (· = q.v)) :
    (fun a => q.pr (y a)) ∈ Submodule.span 𝒪[k] (aux₃ q '' (G : Set (Fin S.rank → D.host.E))) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have h : (fun a => q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x a))) =
        (⟨_, pr_pair_mem q hα⟩ : 𝒪[k]) • aux₃ q x := by
      funext a
      show _ = q.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * q.pr (incA D (x a))
      rw [← map_mul]
      congr 1
      change _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x a)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]; exact Submodule.smul_mem _ _ (splitPointComponent_mem_span_of_lattice_generators q G hG hx)
  | zero =>
    have h : (fun a => q.pr ((0 : Fin S.rank → AE D) a)) = 0 := by funext a; simp
    rw [h]; exact zero_mem _
  | add y z _ _ hy hz =>
    have h : (fun a => q.pr ((y + z) a)) = (fun a => q.pr (y a)) + fun a => q.pr (z a) := by funext a; simp
    rw [h]; exact add_mem hy hz
  | neg y _ hy =>
    have h : (fun a => q.pr ((-y) a)) = -fun a => q.pr (y a) := by funext a; simp
    rw [h]; exact neg_mem hy

def latW (L : GlobalTheory.FinPl.Lat S) : Submodule 𝒪[k] (Fin S.rank → k) where
  carrier := {w | (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)}
  add_mem' := by
    intro x y hx hy
    have h : (fun i => q.sec ((x + y) i)) = (fun i => q.sec (x i)) + fun i => q.sec (y i) := by funext i; simp
    simp only [Set.mem_setOf_eq] at *
    rw [h]; exact add_mem hx hy
  zero_mem' := by
    have h : (fun i => q.sec ((0 : Fin S.rank → k) i)) = 0 := by funext i; simp
    simp only [Set.mem_setOf_eq]
    rw [h]; exact zero_mem _
  smul_mem' := by
    intro c x hx
    have h : (fun i => q.sec ((c • x) i)) = fun i => q.sec (c : k) * q.sec (x i) := by
      funext i; rw [← GlobalTheory.FinPl.FrameLat.sec_mul q]; rfl
    simp only [Set.mem_setOf_eq] at *
    rw [h]
    exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV ((q.int_iff c).1 c.2) hx

theorem mem_latW {L : GlobalTheory.FinPl.Lat S} (w : Fin S.rank → k) :
    w ∈ latW q L ↔ (fun i => q.sec (w i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := Iff.rfl

end GlobalTheory.LocMod.FullLatFrame

namespace GlobalTheory.LocMod.FullLatFrame

end GlobalTheory.LocMod.FullLatFrame
