import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPolynomialPairFunctionalEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem val_mul' (c η : HeckeCharacter ℚ) (v : Ad3.Pl) :
    (toH (c * η)).val v = (toH c).val v * (toH η).val v := Units.ext rfl

