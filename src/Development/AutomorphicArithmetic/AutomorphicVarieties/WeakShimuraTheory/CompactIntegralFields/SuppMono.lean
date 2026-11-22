import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinAl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiesEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrT
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.OverFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FlagFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AffSmulOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GlobalTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.ExistsResidualDatumOverRestrictionToRationals
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.LvSmulOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.MovePs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.EntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.SeedRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.RtFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem supp_mono {R : Type} [CommRing R] {S S' : Finset (ℤ × ℤ)} (h : S ⊆ S') {X : M4 R} (hX : SuppM S X) :
    SuppM S' X := fun i j hij hw => hX i j hij fun hs => hw (h hs)

