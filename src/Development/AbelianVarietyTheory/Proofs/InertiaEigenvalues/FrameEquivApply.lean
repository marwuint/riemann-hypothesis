import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

variable {D : D7} {V : HSp D} {n : ℕ}

def RatFrame (P : principalLevelFrame.RowPsi V n) : Prop :=
  ∀ h, h ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ ∈ Formalism.L2.Theta.GQ V, finHom V γ = finHom V (P.ψ h)

theorem ratF_injective (V : HSp D) : Function.Injective (Bridge.ratF V) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, γ₀, h₀, e⟩ h
  have h1 : finHom V γ = 1 := congrArg Subtype.val h
  have h2 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h3 : ((finHom V γ).1 i j) = inclR (F := D.host.F) (Af D.host.F) (γ₀.1 i j) := by
      have : (matHom V γ).1 i j = inclR (F := D.host.F) (AF D.host.F) (γ₀.1 i j) :=
        (congrArg (fun g : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => g.1 i j) e).symm
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V γ).1 i j) = _
      rw [this]
      simp [inclR]
    have hi : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) := by
      haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
      exact Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    apply hi
    rw [← h3, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  subst h2
  exact Subtype.ext (Subtype.ext (e.symm.trans (map_one _)))

def frameEquiv (P : principalLevelFrame.RowPsi V n) : GAf D.host.E n ≃* Bridge.Gf V :=
  MulEquiv.ofBijective ((finHom V).rangeRestrict.comp P.ψ)
    ⟨fun a b e => P.inj (TopMult.lift_unique (P.into a) (P.into b) e), fun y => by
      obtain ⟨h, hh, e⟩ := TopMult.exists_lift y
      obtain ⟨g, rfl⟩ := P.onto h hh
      exact ⟨g, e⟩⟩

theorem frameEquiv_apply (P : principalLevelFrame.RowPsi V n) (g) : frameEquiv P g = (finHom V).rangeRestrict (P.ψ g) := rfl

theorem RatFrame.iff {P : principalLevelFrame.RowPsi V n} (h : RatFrame P) (g) :
    g ∈ ReciprocityTheory.Aut.GQ D.host.E n ↔ ∃ γ, Bridge.ratF V γ = frameEquiv P g :=
  (h g).trans ⟨fun ⟨γ, hγ, e⟩ => ⟨⟨γ, hγ⟩, Subtype.ext e⟩, fun ⟨γ, e⟩ => ⟨γ.1, γ.2, congrArg Subtype.val e⟩⟩

theorem comap_le_Umax {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsBaseFrame V β Λ 1)
    (Lv : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    (levEnv V β Lv).J.comap (frameEquiv P).toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E n := fun κ hκ =>
  (hP.2 κ).2 ((GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG (Lv := flag1L Lv) ⟨P.into κ, hκ⟩))

section Read

variable {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

def pullForm : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ := ((innerₛₗ ℂ : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ).comp e.toLinearMap).compl₂ e.toLinearMap

theorem pullForm_apply (a b : X.wt.W) : pullForm X e a b = inner ℂ (e a) (e b) := rfl

end Read

end GlobalTheory.FormInner

end
