import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinAl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiesEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FlagFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsResidualRepRestrictionOfLatticeShape

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourChainReduction

open UpperTheory.V.Ws.Chn

theorem inA_of {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
    {P P' : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hq : Supp qQ P.r) (e : P.SameAl P') (h' : InA P') : InA P := by
  have r10 : ∀ g, P.r g 1 0 = 0 := fun g => (e.1 g).trans (h'.1 g 1 0 (by decide) (by decide))
  refine ⟨fun g i j hij hw => ?_, fun v => (e.2 v).symm ▸ h'.2 v⟩
  have : wt i j ∉ qQ ∨ i = 1 ∧ j = 0 ∨ i = 3 ∧ j = 2 := by revert hw; revert i j; decide
  rcases this with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hq g i j hij h1
  · exact r10 g
  · exact al_zero h (qM hq) (r10 g)

end UpperTheory.V.Cu.RankFourChainReduction

