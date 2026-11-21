import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfLeAffineOpenToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonGenericFibreOfMaximalAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroOfToricChartToGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenInteriorContainingToricChartGener
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LocRegRig

theorem isKS_regular_at_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hchart U W hW n v hv hbasis D DW Θ hDW hKS m hm hx0
  obtain ⟨x, hxU, hxm, hxint⟩ := hx0
  haveI := isIso_fst Y
  obtain ⟨x', rfl⟩ := (genι Y).surjective x
  have hbd : x' ∈ genBd Y := mem_genBd_iff.2 fun h => hxint (by
    rw [← SetLike.mem_coe, coe_interior]; exact h)
  have hcl : IsClosed ({x'} : Set (gen Y)) := _root_.GlobalTheory.LocReg.isClosed_singleton_gen E H Dw l Xo c Y U m hm x' hxU hxm
  obtain ⟨k, _, m', d, ξ, t, P, gam, h₀, h₁, h₂, h₃, ⟨φ⟩, h₅, h₆, -⟩ := hchart x' hbd hcl
  subst h₀
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  haveI : CharZero k := _root_.GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  obtain ⟨D', hD', hDlog⟩ := _root_.GlobalTheory.ChartDer.logDer_extend_chartRing E H Dw l Xo c Y U D k m' d ξ hx h₁ h₂
  have hfac := GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := _root_.GlobalTheory.LocReg.BasisPull.exists_basis_pull E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hbasis
  have hab := _root_.GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ h₃
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    h₆.linearIndependent.map' (Submodule.subtype _) (by simp)
  obtain ⟨ΘR, hΘR⟩ := _root_.GlobalTheory.LogKSChart.exists_isKS_of_logDer E H k m' d t P (fun i => gam i) h₅ hlin hab n vR hvR hbR D' hDlog
  obtain ⟨h, hhW, hh0⟩ := _root_.GlobalTheory.LocReg.exists_basicOpen_chartHom_ne_zero E H Dw l Xo c Y U W hW k m' d ξ hx h₃
  obtain ⟨hflat, hcomap⟩ := _root_.GlobalTheory.LocRegFlat.chartHom_flat_comap E H Dw l Xo c Y U k m' d ξ hx h₁ m hm hxm
  have hWc := _root_.GlobalTheory.ModelQC.isCompact_of_le_affineOpen E H Dw l Xo c Y U W.1 (hW.le.trans inf_le_left)
  obtain ⟨g, hg, hs⟩ := _root_.GlobalTheory.LocRegDesc.descent Y.X U W.1 (hW.le.trans inf_le_left) hWc _ (GlobalTheory.LocReg.chartHom Y U ξ hx) hflat m hcomap
    h hhW hh0 (Fin n × Fin n) (fun p => Θ p.1 p.2) (fun p s N e => Dvd.intro _
      (_root_.GlobalTheory.LocRegCmp.ks_chart_eq E H Dw l Xo c Y hpq hsm U W hW n v hv hbasis D DW Θ hDW hKS k m' d ξ hx t φ h₁ h₃ vR hvR hcomp D' hD' ΘR hΘR
        h hhW hh0 p.1 p.2 s N e).symm)
  exact ⟨g, hg, fun a b => hs (a, b)⟩

end GlobalTheory.LocRegRig
