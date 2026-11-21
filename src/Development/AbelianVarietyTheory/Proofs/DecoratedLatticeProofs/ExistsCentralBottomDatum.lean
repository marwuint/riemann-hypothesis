import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlacedBesselPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibility

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.levChi_mul_lev {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  unfold Lev.levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg _ ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

theorem GlobalTheory.MiTop.conj_in_level {G : Type} [Group G] (J : Subgroup G) (χ : G → ℂ)
    (hm : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (h0 : ∀ a, χ a ≠ 0) {k : G} (hk : k ∈ J) (j : G) :
    (j ∈ J ↔ k * j * k⁻¹ ∈ J) ∧ (j ∈ J → χ (k * j * k⁻¹) = χ j) := by
  refine ⟨⟨fun hj => J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk), fun hj => ?_⟩, fun hj => ?_⟩
  · have := J.mul_mem (J.mul_mem (J.inv_mem hk) hj) hk
    rwa [show k⁻¹ * (k * j * k⁻¹) * k = j by group] at this
  · have e := hm _ (J.mul_mem (J.mul_mem hk hj) (J.inv_mem hk)) _ hk
    rw [show k * j * k⁻¹ * k = k * j by group, hm _ hk _ hj, mul_comm (χ k)] at e
    exact (mul_right_cancel₀ (h0 k) e).symm

