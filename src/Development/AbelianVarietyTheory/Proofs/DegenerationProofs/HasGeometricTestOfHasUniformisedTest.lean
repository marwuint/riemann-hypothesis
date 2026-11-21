import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelAdaptedBasisIsModelWithSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.GeoExist

theorem link_smul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (σ : S.J → (u.H S.N).Sec)
    (b : Matrix S.J S.J (FractionRing u.V)) (h : u.Link σ b) (c : FractionRing u.V) (hc : c ≠ 0) :
    u.Link σ (c • b) := by
  intro a v hv
  have hc' : algebraMap (FractionRing u.V) (PadicAlgCl p) c ≠ 0 := (map_ne_zero _).2 hc
  have h₁ := CrdCalc.crd_smul (Units.mk0 _ hc') (h a v hv)
  convert h₁ using 1
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Units.val_mk0, Finset.mul_sum, _root_.mul_assoc]

theorem hasGeo_of_hasU : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  intro hL hT o Ω _ _ _ _ S ρ hB hU p _ y₀ hy Fs
  obtain ⟨u, l, τ, hm, hF⟩ := hU p y₀ hy Fs
  obtain ⟨σ, cls, f, hb⟩ := _root_.GlobalTheory.AdaptedBasis.main hL o Ω S ρ p y₀ u l S.N (le_trans one_le_two S.N_ge) S.J ρ.card
  obtain ⟨md⟩ := _root_.GlobalTheory.ZH.utest_nonempty_mod hL hT o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨b, hd, hl⟩ := _root_.GlobalTheory.ZH.LinkMatrix.exists_link hL o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨c, hc, hs⟩ := _root_.GlobalTheory.ZH.testLattice_eq_span_sections hL o Ω S ρ p y₀ u l τ σ cls md b hB hy hm hl hd
  have hl' := link_smul u σ b hl c hc
  exact ⟨⟨u, l, τ, hm, σ, cls, md, c • b, hl', hs,
    _root_.GlobalTheory.ZH.ClassWeight.row_weight hL hT o Ω S ρ p y₀ u l σ cls f hb (c • b) hl'⟩, hF⟩

end GlobalTheory.ZH.GeoExist
