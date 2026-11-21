import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPred
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlan
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplement

theorem plane_split_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  intro D S Λ q hΛ hneg hq h3
  obtain ⟨x, hx0, hxx⟩ := _root_.GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx D S (q + 1) hneg (by omega) (by omega) h3
  obtain ⟨y, hyy, hxy, hsp⟩ := _root_.GlobalTheory.HypPairSelfDual.exists_partner D S Λ x hΛ hx0 hxx
  obtain ⟨S₁, Λ₁, ι, hPS, hSD, hs⟩ := _root_.GlobalTheory.PlaneCompl.exists_compl D S Λ x y (fun _ => (S.rank - 2 - q, q)) hΛ hxx hyy hxy hsp
  have hrk : S.rank = S₁.rank + 2 := hPS.1
  have hsig := _root_.GlobalTheory.PlaneComplementSig.sig D S S₁ ι x y q hrk hPS.2.1 hxx hyy hxy
    (fun u => ⟨(hPS.2.2.2.2.2.1 u).1, (hPS.2.2.2.2.2.1 u).2⟩) hneg
  have e : S.rank - 2 - q = S₁.rank - q := by omega
  refine ⟨S₁, Λ₁, ι, x, y, hPS, fun τ => ?_, hSD, fun τ => ?_⟩
  · rw [hs]; simp only [e]; exact hsig τ
  · exact hsig _

end GlobalTheory.PlaneComplement

end
