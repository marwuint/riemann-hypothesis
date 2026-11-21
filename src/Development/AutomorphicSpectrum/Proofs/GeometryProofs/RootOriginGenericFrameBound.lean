import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatticePeriodFormIndependentOfModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartExtensionHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FirstFormIffSecondForm
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
import Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndExp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrBCField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Semichar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecondCubicalLawIffClause
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicFixedCard
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Development.WeilBound.CoreStatements.AdicCompleteSpans.MinorC

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {N : Type} [NormedField N]

theorem norm_eq_zpow (j : K →+* N) (hj : ∀ x : V, ‖j (algebraMap V K x)‖ ≤ 1) {π : K} (hπ : vV V π = 1)
    {x : K} (hx : x ≠ 0) : ‖j x‖ = ‖j π‖ ^ vV V x := by
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ
  have hu0 : x * π ^ (-vV V x) ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hv : vV V (x * π ^ (-vV V x)) = 0 := by
    rw [vV_mul hx (zpow_ne_zero _ hπ0), GlobalTheory.ThetaValueIdentityCompare.vV_zpow, hπ]
    ring
  obtain ⟨u, hu, hue⟩ := GlobalTheory.ThetaValueIdentityCompare.exists_unit hu0 hv
  have hn : ‖j (algebraMap V K u)‖ = 1 := by
    obtain ⟨w, rfl⟩ := hu
    have h1 := hj (w : V)
    have h2 := hj ((w⁻¹ : Vˣ) : V)
    have h3 : ‖j (algebraMap V K (w : V))‖ * ‖j (algebraMap V K ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul]
      simp
    nlinarith [norm_nonneg (j (algebraMap V K (w : V))), norm_nonneg (j (algebraMap V K ((w⁻¹ : Vˣ) : V)))]
  rw [hue, map_mul, norm_mul, map_zpow₀, norm_zpow, zpow_neg] at hn
  have hb : ‖j π‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hπ0)
  field_simp at hn
  exact hn

end Val

section Loc

open scoped NormedField Valued

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [h, norm_algebraMap', Padic.norm_p]

theorem zpow_eq_rpow {b : ℝ} (hb : 0 < b) {n m : ℤ} (h : b ^ n = (p : ℝ)⁻¹) :
    b ^ m = (p : ℝ) ^ (-((m : ℝ) / (n : ℝ))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : n ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at h
    have := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hl := congrArg Real.log h
  rw [Real.log_zpow, Real.log_inv] at hl
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (zpow_pos hb m), Real.log_zpow]
  congr 1
  field_simp
  linear_combination (m : ℝ) * hl

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem unitBall : GlobalTheory.BK.IsUnitBall 𝒪[L] L where
  inj := Subtype.val_injective
  mem_range_iff x := ⟨fun ⟨y, h⟩ => h ▸ Valued.integer.mem_iff.1 y.2, fun h => ⟨⟨x, Valued.integer.mem_iff.2 h⟩, rfl⟩⟩

attribute [local instance] unitBall

theorem dvr_fin [FiniteDimensional ℚ_[p] L] : IsDiscreteValuationRing 𝒪[L] ∧ Finite 𝓀[L] := by
  have : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  have hc : CompactSpace 𝒪[L] := by
    have : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [Valued.integer.mem_iff]
    exact isCompact_iff_compactSpace.1 (this ▸ isCompact_closedBall 0 1)
  have : (Valued.v : Valuation L NNReal).RankOne := inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := L)))
  obtain ⟨-, h1, h2⟩ :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.1 hc
  exact ⟨h1, h2⟩

theorem exists_cdvr [FiniteDimensional ℚ_[p] L] :
    ∃ (T : CDVR) (j : T.Fr →+* PadicAlgCl p), T.FinRes ∧ ((p : ℕ) : T.V) ∈ IsLocalRing.maximalIdeal T.V ∧
      (∀ x ∈ L, x ∈ Set.range j) ∧
      ∀ x : T.Fr, x ≠ 0 → ‖j x‖ = (p : ℝ) ^ (-((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ))) := by
  obtain ⟨hd, hf⟩ := dvr_fin L
  have : CompleteSpace L := FiniteDimensional.complete ℚ_[p] L
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[L]) 𝒪[L] :=
    PositivityTheory.CompleteLocalMinorRing.Minor.isAdicComplete_max (K := L) p
  have h0 : CharZero 𝒪[L] := ⟨fun a b h => Nat.cast_injective (R := L) (by
    have := congrArg (algebraMap 𝒪[L] L) h
    simpa using this)⟩
  let T : CDVR := { V := 𝒪[L], dvr := hd, cpl := hc, ch0 := h0 }
  let e : T.Fr ≃+* L := (FractionRing.algEquiv 𝒪[L] L).toRingEquiv
  let j : T.Fr →+* PadicAlgCl p := (algebraMap L (PadicAlgCl p)).comp e.toRingHom
  have hje : ∀ x : T.Fr, j x = ((e x : L) : PadicAlgCl p) := fun _ => rfl
  have hea : ∀ x : 𝒪[L], e (algebraMap 𝒪[L] T.Fr x) = (x : L) := fun x =>
    (FractionRing.algEquiv 𝒪[L] L).commutes x
  have hj : ∀ x : T.V, ‖j (algebraMap T.V T.Fr x)‖ ≤ 1 := fun x => by
    rw [hje]
    erw [hea x]
    exact Valued.integer.norm_le_one x
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_exists_uniformizer T.Fr
  have hπ1 : vV T.V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have hb : 0 < ‖j π‖ := norm_pos_iff.2 ((map_ne_zero j).2 hπ0)
  have hp0 : ((p : ℕ) : T.Fr) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpn : ‖j π‖ ^ vV T.V ((p : ℕ) : T.Fr) = (p : ℝ)⁻¹ := by
    rw [← norm_eq_zpow j hj hπ1 hp0, map_natCast, norm_natCast_p]
  refine ⟨T, j, hf, ?_, fun x hx => ⟨e.symm ⟨x, hx⟩, ?_⟩, fun x hx => ?_⟩
  · refine (PositivityTheory.CompleteLocalMinorRing.Minor.mem_max_iff (K := L)).2 ?_
    rw [map_natCast]
    have : ‖((p : ℕ) : L)‖ = ‖((p : ℕ) : PadicAlgCl p)‖ := rfl
    rw [this, norm_natCast_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  · rw [hje, e.apply_symm_apply]
  · rw [norm_eq_zpow j hj hπ1 hx]
    exact zpow_eq_rpow hb hpn

end Loc

section Main

variable {p : ℕ} [hp : Fact p.Prime]

theorem aeval_mem {σ : Type} {z : σ → PadicAlgCl p} {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L)
    (g : MvPolynomial σ ℤ) : MvPolynomial.aeval z g ∈ L := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C]
    simp [intCast_mem L a]
  | add f g hf hg =>
    rw [map_add]
    exact L.add_mem hf hg
  | mul_X f i hf =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact L.mul_mem hf (hz i)

theorem hasVal_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → PadicAlgCl p} {w : PadicAlgCl p}
    {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hz : ∀ i, z i ∈ L) (h : Small.HasVal y a s z w) : w ∈ L := by
  obtain ⟨dg, dh, g, f, -, -, -, -, h0, e⟩ := h
  rw [eq_div_of_mul_eq h0 e.symm]
  exact L.div_mem (aeval_mem hz g) (aeval_mem hz f)

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Pt

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd
