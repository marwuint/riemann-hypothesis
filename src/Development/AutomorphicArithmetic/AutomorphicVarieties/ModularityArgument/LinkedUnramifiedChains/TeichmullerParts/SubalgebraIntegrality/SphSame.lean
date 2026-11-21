import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SatTUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

private theorem lat {α : Type*} [Lattice α] {Y B f z E : α} (h1 : Y ≤ B) (h2 : Y ≤ f) (h3 : Y ≤ E) :
    Y ⊓ (B ⊓ f ⊓ z ⊓ E) = Y ⊓ z :=
  le_antisymm (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    (le_inf inf_le_left (le_inf (le_inf (le_inf (inf_le_left.trans h1) (inf_le_left.trans h2)) inf_le_right)
      (inf_le_left.trans h3)))

private theorem eig_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {a b : ℂ} {F : M} (h0 : F ≠ 0)
    (hT : T F = a • F) (hF : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hF
  have h1 : (T - b • (1 : Module.End ℂ M)) F = (a - b) • F := by
    simp [hT, sub_smul]
  have h : ∀ i : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ i) F = (a - b) ^ i • F := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, pow_succ']
  rw [h k] at hk
  by_contra hne
  exact smul_ne_zero (pow_ne_zero k (sub_ne_zero.2 hne)) h0 hk

private theorem eig_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {b : ℂ} {F : M}
    (hT : T F = b • F) : F ∈ T.maxGenEigenspace b :=
  (Module.End.mem_maxGenEigenspace T b F).2 ⟨1, by simp [hT]⟩

private theorem eig_le {M I : Type*} [AddCommGroup M] [Module ℂ M] (T : I → Module.End ℂ M) (ev : I → ℂ) (i : I) (a : ℂ)
    (O Y Y' : Submodule ℂ M) (hne : Y ⊓ (O ⊓ ⨅ i, (T i).maxGenEigenspace (ev i)) ≠ ⊥)
    (h1 : ∀ F ∈ Y, T i F = a • F) (h2 : ∀ F ∈ Y', T i F = a • F) : Y' ≤ (T i).maxGenEigenspace (ev i) := by
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hFe : F ∈ (T i).maxGenEigenspace (ev i) :=
    (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hF).2).2 i
  have hae : a = ev i := eig_eq _ hF0 (h1 F (Submodule.mem_inf.1 hF).1) hFe
  intro F' hF'
  exact eig_mem _ (hae ▸ h2 F' hF')

private theorem scalar (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GLw n w)) (j : ℕ) :
    ∃ a : ℂ, ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v := by
  by_cases h : GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w n)
  · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred h
    obtain ⟨-, a, -, ha, -⟩ := UpperTheory.V.Hi.satT L n w τ B hB
    exact ⟨a j, ha j⟩
  · refine ⟨0, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra h0
      rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
      exact h ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩)
    simp [hv0]

end UpperTheory.V.Z.J.D
