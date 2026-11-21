import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentreComm

open GlobalTheory.Mem.AutSpace

variable {D : D7} {θ : InfFam D} {V : HSp D}

variable (θ V) in

def CommOnSm (A B : (GA D V → ℂ) → (GA D V → ℂ)) : Prop := ∀ f ∈ SmFun θ V, A (B f) = B (A f)

theorem lin_sum {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {α : Type} (s : Finset α)
    (g : α → GA D V → ℂ) (hg : ∀ a ∈ s, g a ∈ SmFun θ V) : T (∑ a ∈ s, g a) = ∑ a ∈ s, T (g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using hT.smul 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (hg a (by simp)) _
      (Submodule.sum_mem _ fun b hb => hg b (by simp [hb])), ih fun b hb => hg b (by simp [hb])]

theorem comm_foldr {T : (GA D V → ℂ) → (GA D V → ℂ)} {α : Type} (A : α → (GA D V → ℂ) → (GA D V → ℂ))
    (l : List α) (hl : ∀ a ∈ l, LinOnSm θ V (A a)) (hc : ∀ a ∈ l, CommOnSm θ V T (A a)) :
    CommOnSm θ V T fun f => l.foldr (fun a g => A a g) f := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro f hf
    have h2 := linOnSm_foldr A l fun b hb => hl b (by simp [hb])
    simp only [List.foldr_cons]
    rw [hc a (by simp) _ (h2.mem f hf), ih (fun b hb => hl b (by simp [hb])) (fun b hb => hc b (by simp [hb])) f hf]

theorem comm_gelf {T : (GA D V → ℂ) → (GA D V → ℂ)} (hT : LinOnSm θ V T) {τ : D.what₂.Tau}
    (hc : ∀ Z, CommOnSm θ V T (RderC θ V τ Z)) (k : ℕ) : CommOnSm θ V T (gelf θ V τ k) := by
  have hl : ∀ idx : Fin (k + 1) → Fin V.rank, ∀ S ∈ (List.ofFn fun a : Fin (k + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), LinOnSm θ V S ∧ CommOnSm θ V T S := fun idx S hS => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hS
    exact ⟨linOnSm_RderC τ _, hc _⟩
  intro f hf
  simp only [gelf]
  rw [lin_sum hT _ _ fun idx _ => (linOnSm_foldr (fun S => S) _ fun S hS => (hl idx S hS).1).mem f hf]
  exact Finset.sum_congr rfl fun idx _ =>
    comm_foldr (fun S => S) _ (fun S hS => (hl idx S hS).1) (fun S hS => (hl idx S hS).2) f hf

theorem gelf_RderC (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (k : ℕ) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    CommOnSm θ V (gelf θ V τ k) (RderC θ V τ' Z) := by
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
  simp only [RderC]
  rw [(linOnSm_gelf τ k).add _ (Rder_mem hf h1) _ (Submodule.smul_mem _ _ (Rder_mem hf h2)), (linOnSm_gelf τ k).smul,
    GlobalTheory.CuspLie.gelf_Rder hθ h1 hf, GlobalTheory.CuspLie.gelf_Rder hθ h2 hf]

end GlobalTheory.CentreComm

end
