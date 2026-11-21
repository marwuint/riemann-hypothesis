import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalChartResidueFieldDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyHasPointRigidCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenPartClassifiedMonomialBoundaryFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPointRigidBoundaryFamilyOfRigidCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDataRigidAlongStratum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem isTautB_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi k _ m e C hC hms
  obtain ⟨hm, hs⟩ := hms
  have hB : GlobalTheory.Mum.Base (ChartRing k m e) := GlobalTheory.ChartQF.base_chartRing C.toFam
  have hR : HasRigidCoords C := _root_.GlobalTheory.UCanon.canon_hasRigidCoords Xo c φ (ChartRing k m e) hB C hC
  obtain ⟨hft, hdim⟩ := GlobalTheory.T.canonicalChart_residueField_dimension Xo c φ C hC
  obtain ⟨N, s, ε, τ₀, h1, h2, h3, h4, -⟩ := id hR
  exact ⟨⟨hm, hs, _root_.GlobalTheory.UCanon.OpenPart.openCls Xo c φ _ hB C, _root_.GlobalTheory.UCanon.inj_of_canon Xo c φ hpq hfan hnsi _ hB C hC,
    ⟨_root_.GlobalTheory.UCanon.isRigid_canon Xo c φ _ hB C hC, _root_.GlobalTheory.PtRigid.pointRigid_of_hasRigidCoords Xo c φ _ C hR, hft⟩, ⟨N, s, ε, τ₀, h1, h2, h3, h4⟩, hdim⟩, hR⟩

end GlobalTheory.UCanon
