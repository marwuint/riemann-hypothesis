import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SomeInOfLocZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Labels
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ExistsTameTowerOkTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NegSqPowNeOneOfOddOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LatSix
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SuppMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinPs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsResidualRepRestrictionOfLatticeShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.X2
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LayerEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SpaceEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChCore

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem conj_trans {H R : Type} [Group H] [CommRing R] {r r' r'' : H →* M4 R} (h : IsConj4 r r') (h' : IsConj4 r' r'') :
    IsConj4 r r'' := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨v * u, fun g => by rw [hv, hu, mul_inv_rev, Units.val_mul, Units.val_mul]; simp only [mul_assoc]⟩

