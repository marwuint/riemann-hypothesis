import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspFam

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions GlobalTheory.CuspRep Blocks
theorem CGTrueT.blocksUnique (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hJ : GlobalTheory.Published.JacquetShalikaRigidity)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) :
    BlocksUnique D := by
  intro Sig Sig' h _ _ e
  have := host_isCMField D.host
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  have h1 := fun p hp => h p (List.mem_append_left Sig' hp)
  have h2 := fun p hp => h p (List.mem_append_right Sig hp)
  exact Multiset.coe_eq_coe.2 ((perm_of_split hC (GlobalTheory.RowPar.isobaricRigid_of_jacquetShalika hJ (_root_.GlobalTheory.HeightCounting.Blocks.readsCusp_alt hF C))
    (_root_.GlobalTheory.HeightCounting.Blocks.cuspFam_alt_alt hF C hG (l := 2) ι) (fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1⟩) (fun p hp => ⟨(h2 p hp).1, (h2 p hp).2.1⟩)
    ⟨fun p hp => (h1 p hp).2.2.1, fun p hp => (h1 p hp).2.2.2⟩ ⟨fun p hp => (h2 p hp).2.2.1, fun p hp => (h2 p hp).2.2.2⟩
    (Filter.Eventually.of_forall e)).map _)
end GlobalTheory.HeightCounting
end
end
