import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSizesOfStdKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamRowsSizes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacte
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.DefSide

open Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory in

theorem full_rank {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (tie : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) (hCh : ChosenE Fm 3 CH) :
    NuFullF Fm ∧ J.MuRank Fm := by
  have tT := (family_conditions_of_layer_two Fm tie).2.2
  have h := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds Formalism.L2.GlobalTheoryTheory.LemB.second_branch_all_members
  obtain ⟨hT2, hT5⟩ := Formalism.MainNotions.Wire.family_theorems_two_and_five Fm h.1 h.2.1 (hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice)
    (tT.mono fun D u hS ht => Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.hecke_ramified_zero_all D u hS ht) h.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
  exact muRank_items Fm 3 (by norm_num) hT2 hT5 hTu cPr

theorem wts_eq {X X' : Formalism.L2.Col.Fields} (h : X = X') {P : Formalism.L2.Col.Primes X} {P' : Formalism.L2.Col.Primes X'} (hP : HEq P P')
    {R R' : Ranks} (hR : R = R') : Formalism.L2.Col.Wts X P.Word R = Formalism.L2.Col.Wts X' P'.Word R' := by
  subst h; cases hP; subst hR; rfl

end GlobalTheory.Fc.RL.DefSide

end
