import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpacesNormHasFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem exists_fixed (B : Base) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic ℚ z) :
    ∃ B' : Base, B'.toPre = B.toPre ∧ B'.KsC = B.KsC ∧ ∀ z ∈ S, z ∈ B'.fixedCoefficientFieldInComplex := by
  obtain ⟨B', h, h'⟩ := BaseEnl.exists_enl B S hS
  refine ⟨{ B' with LL0 := ⊤, coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm, Ks_le := le_top,
                    rootOfUnity_eightQ_mem_coeffGaloisSubfield := B'.rootOfUnity_eightQ_mem_coeffGaloisSubfield.imp fun _ hz => ⟨trivial, hz.2⟩ }, h.1, h.KsC_eq, fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := h' z hz
  exact ⟨x, trivial, hx⟩

end GlobalTheory.Mem.Top.Inh

end
