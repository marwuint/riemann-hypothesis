import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial

namespace GlobalTheory.TypeAbove

theorem conj_over_split (D : D7) {p : ℕ} {w w' : PlE D.host} (hw : w ∈ placesOver D.host.E p)
    (hs : IsSplitPl D.host w) (hc : IsConjPl D.host w w') :
    w' ∈ placesOver D.host.E p ∧ IsSplitPl D.host w' := by
  have h := (GlobalTheory.ConjPlaceOff.isConjPl_iff D w w').1 hc
  refine ⟨?_, ?_⟩
  · have e := (h ((p : ℕ) : 𝓞 D.host.E)).1 hw
    rwa [map_natCast] at e
  · obtain ⟨x, hx, hcx⟩ := (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w).1 hs
    exact (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w').2 ⟨_, (h x).1 hx, fun h' => hcx ((h _).2 h')⟩

end GlobalTheory.TypeAbove
