import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersTwistedAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CrossGOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SecDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

