import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShift
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenDecompositionExactSequence
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartConst

theorem lieMult_constant_along_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X) (P : AbPart 𝔐.t z), ∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult P.tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult P.tB.act (spMap g) τ q') := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z P
  obtain ⟨ρ, hρ, hdet⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point E H D l Xo c Y S Ω K J y 𝔐 L z
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart E H 𝔐.X 𝔐.t L z P
  refine ⟨ρ, D.p - r, D.q - r, hρ, fun k _ _ g τ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := (hdet k g τ).1 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.p).mpr h1
    exact (hr k g τ D.p h2).2
  · have h1 := (hdet k g τ).2 h
    have h2 := (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ P.m.cart P.m.act k (spMap g) τ D.q).mpr h1
    exact (hr k g τ D.q h2).2

end GlobalTheory.CompanionTheory.Ar.AbPartConst
