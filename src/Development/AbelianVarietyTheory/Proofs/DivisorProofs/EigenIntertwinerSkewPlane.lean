import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvUniq.LocFin

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev ind (w : Pl F) : (κ → Fv F w) → ℂ := Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

def archPt (a : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), 0)

theorem evFin_archPt (a : κ → mixedEmbedding.mixedSpace F) (w : Pl F) (i : κ) : evFin F w (archPt a i) = 0 := by
  change (evalV F w) (0 : Af F) = 0
  exact map_zero _

theorem evI_archPt (a : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPt a i) = a i := by
  simp [evI, archPt]

theorem cancel (v : Pl F) (g : SInf F κ) (hg : g ≠ 0) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hrt : ∀ ψ₀ : (κ → Fv F v) → ℂ, tens (evFin F v) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update ind v ψ₀))
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hg
    exact ⟨a, by simpa using ha⟩
  have hx0 : r (archPt a) = g a := by
    have e := congrFun (hrt (fun _ => 1)) (archPt a)
    simp only [tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i => evI F (archPt a i)) = a := funext fun i => evI_archPt a i
    have hP : (∏ᶠ w, Function.update (ind (κ := κ)) v (fun _ => 1) w fun i => evFin F w (archPt a i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [evFin_archPt, ind]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrz : r (archPt a + z) = g a := by rw [hr _ z hz, hx0]
  have hev : (fun i => evFin F v ((archPt a + z) i)) = y := by
    funext i
    rw [Pi.add_apply, map_add, evFin_archPt, zero_add]
    exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun h (archPt a + z)
  simp only [tens, hev, hrz] at e
  exact mul_right_cancel₀ ha e

end GlobalTheory.ThK.EvUniq.LocFin
