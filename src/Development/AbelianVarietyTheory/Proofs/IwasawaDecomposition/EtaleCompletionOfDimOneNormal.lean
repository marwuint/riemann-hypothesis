import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 0 3
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

end GlobalTheory.CdvrExt
