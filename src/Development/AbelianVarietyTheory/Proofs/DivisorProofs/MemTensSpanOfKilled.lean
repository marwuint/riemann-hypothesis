import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.RealLift GlobalTheory.KFixIrr GlobalTheory.FockAlg

namespace GlobalTheory.DegKeep

section Lift

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hw_of_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ :=
  GlobalTheory.CommonQuot.map_hw L h hv

theorem joint_lift {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hL : ∀ w, IsKLieAct (a w)) (hw : ∀ w v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (a w) μ)
    (hc : ∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v))
    (W N : Submodule ℂ V) [FiniteDimensional ℂ W] (sW : ∀ w, KStable (a w) W) (sN : ∀ w, KStable (a w) N)
    (μ : ι → Ix p q → ℚ) (T : V) (hT : T ∈ W)
    (h1 : ∀ w c, a w (Eab c c) T - ((μ w c : ℚ) : ℂ) • T ∈ N) (h2 : ∀ w c d, posC c d → a w (Eab c d) T ∈ N) :
    ∃ T' ∈ W, T - T' ∈ N ∧ ∀ w, T' ∈ hwSub (a w) (μ w) := by
  have key : ∀ s : Finset ι, ∃ T' ∈ W, T - T' ∈ N ∧ ∀ w ∈ s, T' ∈ hwSub (a w) (μ w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨T, hT, by simp, by simp⟩
    | insert w s hws ih =>
      obtain ⟨T', hT'W, hTN, hT's⟩ := ih
      let Ws : Submodule ℂ V := W ⊓ ⨅ w' ∈ s, hwSub (a w') (μ w')
      have mem : ∀ v, v ∈ Ws ↔ v ∈ W ∧ ∀ w' ∈ s, v ∈ hwSub (a w') (μ w') := fun v => by
        simp only [Ws, Submodule.mem_inf, Submodule.mem_iInf]
      haveI : FiniteDimensional ℂ Ws := Submodule.finiteDimensional_of_le (inf_le_left : Ws ≤ W)
      have sWs : KStable (a w) Ws := fun Z hZ v hv => by
        rw [mem] at hv ⊢
        refine ⟨sW w Z hZ v hv.1, fun w' hw' => hw_of_comm (fun Z' v => ?_) (hv.2 w' hw')⟩
        exact hc w w' (fun e => hws (e ▸ hw')) Z Z' v
      obtain ⟨C, sC, hNC, hNCW⟩ := GlobalTheory.BlockReps.exists_compl (hL w) sWs (fun v _ => hw w v) (Ws ⊓ N) inf_le_left
        (GlobalTheory.BlockReps.stable_inf sWs (sN w))
      have hCW : C ≤ Ws := by rw [← hNCW]; exact le_sup_right
      have hT'' : T' ∈ (Ws ⊓ N) ⊔ C := by rw [hNCW, mem]; exact ⟨hT'W, hT's⟩
      obtain ⟨n, hn, c, hcC, rfl⟩ := Submodule.mem_sup.1 hT''
      have hTc : T - c ∈ N := by
        have := N.add_mem hTN hn.2
        rwa [show T - (n + c) + n = T - c by abel] at this
      have hz : ∀ v ∈ C, v ∈ N → v = 0 := fun v h h' => by
        have : v ∈ (Ws ⊓ N) ⊓ C := ⟨⟨hCW h, h'⟩, h⟩
        rwa [hNC, Submodule.mem_bot] at this
      refine ⟨c, ((mem c).1 (hCW hcC)).1, hTc, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [GlobalTheory.CommonQuot.mem_hwSub']
        refine ⟨fun d => hz _ (C.sub_mem (sC _ (GlobalTheory.CommonQuot.isKC_diag' d) c hcC) (C.smul_mem _ hcC)) ?_,
          fun d e hde => hz _ (sC _ (GlobalTheory.CommonQuot.isKC_pos' hde) c hcC) ?_⟩
        · have := N.sub_mem (h1 w' d) (N.sub_mem (sN w' _ (GlobalTheory.CommonQuot.isKC_diag' d) _ hTc)
            (N.smul_mem ((μ w' d : ℚ) : ℂ) hTc))
          rw [map_sub, smul_sub] at this
          convert this using 1; abel
        · have := N.sub_mem (h2 w' d e hde) (sN w' _ (GlobalTheory.CommonQuot.isKC_pos' hde) _ hTc)
          rw [map_sub] at this
          convert this using 1; abel
      · exact ((mem c).1 (hCW hcC)).2 w' hw'
  obtain ⟨T', h, h', h''⟩ := key Finset.univ
  exact ⟨T', h, h', fun w => h'' w (Finset.mem_univ w)⟩

end Lift

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

def actAt {p q : ℕ} (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (w : ι) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : ι, V) where
  toFun Z := atPl (V := fun _ : ι => V) w (a Z)
  map_add' Z Z' := by rw [map_add, GlobalTheory.RealLift.Main.atPl_add]
  map_smul' c Z := by rw [map_smul, GlobalTheory.RealLift.Main.atPl_smul]; rfl

theorem actAt_apply {p q : ℕ} (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (w : ι) (Z : Mat p q) :
    actAt a w Z = atPl (V := fun _ : ι => V) w (a Z) := rfl

def intersection_update_fsHerm_neg_one (f : ι → V) (w : ι) : V →ₗ[ℂ] ⨂[ℂ] _ : ι, V := (PiTensorProduct.tprod ℂ (s := fun _ : ι => V)).toLinearMap f w

theorem position_apply (f : ι → V) (w : ι) (v : V) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

end Tensor

section Fock

open MvPolynomial

variable {P Q R S : ℕ}

theorem deg_le_of_harm {μ : Ix R S → ℚ} {f : Formalism.BasicNotions.TH.Pol P Q R S} (hh : f ∈ harm2 P Q R S)
    (hf : f ∈ hwSub (fockAct2 P Q R S) μ) : f.totalDegree ≤ ⌊degW (cPair P Q) μ⌋₊ := by
  by_cases hne : f = 0
  · simp [hne]
  obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  have hOT := GlobalTheory.BlockReps.ofType_hw GlobalTheory.FockAlg.MinFirst.kLie2 sW hP ⟨hne, hf⟩
  obtain ⟨d, hd, hhom⟩ := (harmonic_homog_of_type P Q R S).2 μ f hne hOT hh
  rw [mem_homogeneousSubmodule] at hhom
  rw [← hd, Nat.floor_natCast, hhom.totalDegree hne]

theorem stable_restrict (d : ℕ) : KStable (fockAct2 P Q R S) (restrictTotalDegree (Ln P Q R S) ℂ d) := fun Z hZ f hf => by
  rw [mem_restrictTotalDegree] at hf ⊢
  exact (LowStable.mem_nonRaising.1 (LowStable.fockAct2_mem Z hZ) f).trans hf

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

end Fock

end GlobalTheory.DegKeep

end
