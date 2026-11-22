import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.WeilBound.CoreStatements.AutomorphicKernels.TemperedUnitNorm.NormEqOneOfTemperedRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
namespace GlobalTheory.GalAllPlaces
end GlobalTheory.GalAllPlaces
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.CsdTwistGal
end GlobalTheory.CsdTwistGal
namespace GlobalTheory.TempSatGal
theorem weight_eq_alt_alt {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {χ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) (m : (E →+* ℂ) → Multiset ℂ) (s : ℝ)
    (hcard : ∀ τ, (m τ).card = a) (hinf : ∀ τ, (CG.mk π).infChar τ = (m τ).map (· + (s : ℂ)))
    (hconj : ∀ τ, m (ComplexEmbedding.conjugate τ) = (m τ).map Neg.neg) :
    (wt : ℝ) = (a : ℝ) - 1 - 2 * s := by
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ι.toRingHom.comp (ι.symm.toRingHom.comp τ0) = τ0 := by ext x; simp
  set τ : E →+* Qbar l := ι.symm.toRingHom.comp τ0 with hτdef
  set X : Multiset ℂ := (HT τ).map (fun n : ℤ => (n : ℂ)) with hXdef
  have hX : X = (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + (-1) * z) := by
    rw [hXdef, H.weights τ, hτ, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hY : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      X.map (fun z => (wt : ℂ) + (-1) * z) := by
    rw [H.weights_conj, hXdef, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun n _ => ?_
    simp only [Function.comp_apply]; push_cast; ring
  have hZ : (HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom)).map (fun n : ℤ => (n : ℂ)) =
      (m τ0).map (fun z => (((a : ℂ) - 1) / 2 - s) + 1 * z) := by
    rw [H.weights, comp_complexConj, hτ, hinf, hconj, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]; ring
  have hcX : (X.card : ℂ) = a := by rw [hX, Multiset.card_map, hcard]
  have e := congrArg Multiset.sum (hY.symm.trans hZ)
  rw [sum_map_affine, sum_map_affine, hcX, hX, sum_map_affine, hcard] at e
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have h : (wt : ℂ) = (a : ℂ) - 1 - 2 * (s : ℂ) := by
    apply mul_left_cancel₀ ha0
    linear_combination e
  exact_mod_cast h
end GlobalTheory.TempSatGal
end
end
end
