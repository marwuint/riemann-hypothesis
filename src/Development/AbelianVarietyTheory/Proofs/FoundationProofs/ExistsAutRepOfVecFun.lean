import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfColW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjectiveDetPowMulDualWeyl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutRec

theorem continuous_coord_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    Continuous (coord (E := E) τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_cEmb_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_coord_emb τ))).comp GlobalTheory.DefU.continuous_cInf

end GlobalTheory.AutRec

end
