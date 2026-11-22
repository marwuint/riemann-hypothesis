import Mathlib
import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
set_option maxSynthPendingDepth 1

noncomputable section

open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal

namespace GroundTheory.BlockD

namespace ThmBHecke

section Single

variable {K : Type} [Field K] [NumberField K]

open Classical in

def finSingleOne (w : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K :=
  ⟨Pi.single (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu ↦ ?_)
    by_contra h
    exact hu (by rw [Pi.single_eq_of_ne h]; exact zero_mem _)⟩

theorem finSingleOne_self (w : HeightOneSpectrum (𝓞 K)) : finSingleOne w w = 1 := by
  classical
  exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 K) ↦ u.adicCompletion K) w 1

end Single

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idemAt (P : HeightOneSpectrum (𝓞 E)) : 𝔸[E] := (0, finSingleOne P)

@[simp]
theorem idemAt_fst (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).1 = 0 := rfl

@[simp]
theorem idemAt_snd_self (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).2 P = 1 := finSingleOne_self P

theorem adeleMap_snd_apply (a : AF F) (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E a).2 w = completionMap (below F w) w (a.2 (below F w)) :=
  rfl

section Conj

variable {σ : E →ₐ[F] E}

theorem cA_tmul (a : AF F) (x : E) : cA σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl

theorem cA_incA (x : E) : cA σ (incA F E x) = incA F E (σ x) := rfl

end Conj

end ThmBHecke

end GroundTheory.BlockD
