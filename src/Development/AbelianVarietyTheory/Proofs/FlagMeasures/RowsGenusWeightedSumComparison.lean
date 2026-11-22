import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumEqSumOrbitReps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseLatticeConstructionHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem cardE (α : Type) [Nonempty α] :
    ENNReal.ofReal ((Nat.card α : ℝ)⁻¹) = ((ENat.card α : ℕ∞) : ℝ≥0∞)⁻¹ := by
  rcases finite_or_infinite α with h | h
  · have h0 : 0 < Nat.card α := Nat.card_pos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]
    simp
  · rw [Nat.card_eq_zero_of_infinite, ENat.card_eq_top_of_infinite]
    simp

set_option maxHeartbeats 4000000 in
theorem rowsOrbC : GlobalTheory.TypeAsm.RowsOrbC := by
  intro D large₂ X Y u hS W HW hEmb φ hφ Λ₀ hΛ₀
  obtain ⟨e, he, heX⟩ := _root_.GlobalTheory.RowsOrb.ub_equiv_model D X u W HW hEmb
  have hlat := GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart D X u W e heX
  set M₀ := GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ₀) with hM₀
  obtain ⟨hψ, hgen, horb⟩ := _root_.GlobalTheory.Mass.Transp.orbSum_img D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he φ hφ M₀
  obtain ⟨hcm, -, -, -, hf, -, -, -, -, -, -, -, hTu⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hS
  obtain ⟨hTp, hsp⟩ := hTu u
  have hl0 := _root_.GlobalTheory.TypeAsm.lat0C D large₂ X Y u hS W HW hEmb Λ₀ hΛ₀
  rw [hlat Λ₀] at hl0
  obtain ⟨hM₀i, hM₀d⟩ := _root_.GlobalTheory.Mass.Transp.discModule_transport D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he M₀ _ hl0.1 hl0.2
  have hbs : (GlobalTheory.RowsOrb.hb X).IsSymm := ⟨fun a b => (VS D).herm.eq (a : (VS D).V) (b : (VS D).V)⟩
  have hz : GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.zb X u) = -((Tu D u : ℕ) : D.host.E) := X.zu_norm u
  have hrm := GlobalTheory.Mass.RowMean.main D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) hcm hbs (Tu D u)
    (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.Ub X u) hTp hsp hz rfl (_root_.GlobalTheory.RowsOrb.pd_hU D X u) M₀ hM₀i hM₀d
    (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  simp only [hlat, ← hM₀, hgen]
  rw [horb, ← hf]
  refine Eq.trans ?_ hrm
  obtain ⟨hst, hinv⟩ := _root_.GlobalTheory.RowsOrb.StabSet.main D X u M₀ (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  have hinj : ∀ a ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      ∀ b ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      GlobalTheory.RowsOrb.Lmap X u a = GlobalTheory.RowsOrb.Lmap X u b → a = b := by
    intro a ha b hb hab
    exact _root_.GlobalTheory.RowsOrb.rows_eq_of_conj D large₂ X Y u hS a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 1 ((one_smul (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u a)).trans hab)
  refine Eq.trans ?_ (GlobalTheory.Mass.orbSum_eq_sum_reps (GlobalTheory.RowsOrb.Gz X u) (Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X))
    {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} (fun L => φ (GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L))) hst (fun g L => hinv g L)
    (((Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀)).image (GlobalTheory.RowsOrb.Lmap X u)) ?_ ?_).symm
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    congr 1
    show ENNReal.ofReal ((Nat.card (autLz D (X.Fu u) Λ) : ℝ)⁻¹) = _
    rw [_root_.GlobalTheory.RowsOrb.card_autLz D large₂ X Y u hS Λ (Finset.mem_filter.1 hΛ).1, cardE]
  · intro L hL
    obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hΛr, hΛg⟩ := Finset.mem_filter.1 hΛ
    obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.RowsOrb.Basic.lmap_basic D large₂ X Y u hS Λ hΛr
    exact ⟨h1, h2, h3, hΛg⟩
  · intro L hL
    obtain ⟨Λ, hΛ, g, hg⟩ := _root_.GlobalTheory.RowsOrb.exists_row_of_unimod D large₂ X Y u hS L hL.1 hL.2.1 hL.2.2.1
    refine ⟨GlobalTheory.RowsOrb.Lmap X u Λ, ⟨Finset.mem_image.2 ⟨Λ, Finset.mem_filter.2 ⟨hΛ, ?_⟩, rfl⟩, g, hg⟩, ?_⟩
    · have := hst g⁻¹ L hL
      erw [← hg, inv_smul_smul] at this
      exact this.2.2.2
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.1 hy
      congr 1
      exact _root_.GlobalTheory.RowsOrb.rows_eq_of_conj D large₂ X Y u hS Λ' (Finset.mem_filter.1 hΛ').1 Λ hΛ (g⁻¹ * g') (by erw [mul_smul, hg', ← hg, inv_smul_smul])

end GlobalTheory.RowsOrb
