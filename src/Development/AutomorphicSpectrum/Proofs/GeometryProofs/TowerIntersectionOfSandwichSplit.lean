import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatUnitOfSplitRootLines
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HasReferenceOfSandwichAllPrimes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInput
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopGood

theorem tower_intersection_of_ample_flat (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (T : Top.RootTower Ψ (p + q)) (II : IntersectionSystem) (R : T.Comp → Top.RootModel Ψ (p + q))
    (hII : IsIntersectionSystem II) (hR : Ht.HasRef T R)
    (h : ∀ a, Ht.AmpleQ (R a).y (R a).A.a ∧ Ht.FlatUnit (R a) ∧ Ht.FibreInput (j := p) (k := q) (R a)) :
    T.I5 II := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  exact _root_.GlobalTheory.CompanionTheory.Ar.Ht.TopLower.i5_of_hasRef_of_fibreInput Ψ j k T II R hII hR h

theorem tower_good_of_sandwich_split : Top.Given → Flat.FlatLineGenerator → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T)
    (II : IntersectionSystem), IsIntersectionSystem II → SplitComps Y →
    (∀ B a, ∀ p ∈ g.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (g.Or B a).𝔐 p κ) → T.I5 II ∧ T.I6 II := by
  intro hG hA E _ _ _ H D l Xo c Y _ T g II hII hsp hS
  obtain ⟨⟨hI, hab, -⟩, -, hext, -, hres, -, -, -, hsl, -⟩ := hG
  have hR : Ht.HasRef T g.R := _root_.GlobalTheory.CompanionTheory.Ar.OrRef.has_ref E H D l Xo c Y T g hS
  have hj := g.j_eq
  have h1 := T.j_pos
  have h2 := T.j_lt
  have hp : 1 ≤ D.p := by omega
  have hq : 1 ≤ D.q := by omega
  have hN : 1 ≤ D.p + D.q := by omega
  refine ⟨tower_intersection_of_ample_flat _ D.p D.q hp hq T II g.R hII hR fun a => ⟨g.ample a, ?_, ?_⟩,
    _root_.GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper _ _ T II g.R hII hR⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Ht.FlatGen.flat_unit_of_root_lines hA E H D l Xo c Y ∅ (g.R a) (g.refOr a).𝔐 (g.refOr a).Fl (g.refOr a).e hN hsp
      (g.refOr a).lines
  · exact _root_.GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput hab hI hres hext hsl E H D l Xo c Y ∅ (g.R a) (g.refOr a).𝔐 (g.refOr a).Fl (g.refOr a).e hN
      (g.refOr a).lines

end GlobalTheory.CompanionTheory.Ar.TopGood
