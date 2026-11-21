import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotFixingFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

end Ideles

end GlobalTheory.ArtinTransfer

end
