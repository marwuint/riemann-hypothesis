import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NonemptyComponentModel
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MuFrameNormLine
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationSetting
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsTiedRegularSetting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeft
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionLimit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S : LogLogRegularisationSetting M Dc.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ z, 0 ≤ U z) ∧ (∀ z ∈ Dc.Xo, ∀ t : K → ℂ, (∀ k, t k ≠ 0) → U (torusSmul t z) = U z) ∧ S.IsTied ∧ S'.IsTied ∧ ConjU S' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  obtain ⟨U, hU, h0, hT, hC, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨hp1, -, hp2, hc2⟩ := GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨hb, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd.corr_bdd hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨-, -, hL, hO⟩ := _root_.LevelTowerAlt.mu_frame_norm_line K J II (CMType H) Ω W Dc Hd
  obtain ⟨M⟩ := _root_.LevelTowerAlt.nonempty_component_model K J II (CMType H) Ω W Dc
  obtain ⟨S, hS⟩ := _root_.LevelTowerAlt.exists_tied_regular_setting K J II (CMType H) Ω W Dc Hd M hp1
  obtain ⟨S', hS', hJ⟩ := _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_setting K J II (CMType H) Ω W Dc Hd M (corrW Hd U)
    (fun z hz a ha => by
      have := hL z hz a ha
      simp only [corrW, hT z a ha, this]
      ring)
    hp2 hc2 hb
    (fun z hz => by
      have := hO z hz
      simp only [corrW, hC z, this])
  exact ⟨U, M, S, S', hU, h0, fun z _ t ht => hT z t ht, hS, hS', hJ⟩
