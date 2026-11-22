import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩

end GlobalTheory.FieldSize
