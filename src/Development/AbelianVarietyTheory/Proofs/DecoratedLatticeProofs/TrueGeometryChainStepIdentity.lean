import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeStepValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexStep
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegral

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.Fam
namespace VolMid

theorem index_pi_univ' {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_of_pi {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ']
  rfl

end VolMid

open VolMid

end GlobalTheory.Fam
