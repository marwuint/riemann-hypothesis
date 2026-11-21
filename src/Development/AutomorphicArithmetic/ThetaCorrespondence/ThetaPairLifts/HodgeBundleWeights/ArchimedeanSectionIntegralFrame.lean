import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitAtEqualCharacteristicPoints

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
namespace GlobalTheory.FlatCore.Bdry
theorem nval_evI_eq_zero_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := _root_.GlobalTheory.T.boundary_isUnit_at_eqChar_points hP hQ2 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := _root_.GlobalTheory.FlatCore.archSec_exists_eq_smul E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp
end GlobalTheory.FlatCore.Bdry
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  exact @_root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt
end
