import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesDerivationEqPderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesInjectiveLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesIsAdicCompleteMapCOfNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsCommuteOfCommGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := _root_.GlobalTheory.Heat.liftDer_isDerivation R G D W d hd hW
  choose δ hδ using fun a => _root_.GlobalTheory.StalkDerField.exists_stalk_derivation G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := _root_.GlobalTheory.StalkDerField.exists_stalk_derivation G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      _root_.GlobalTheory.InvFieldComm.invField_comm R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← _root_.GlobalTheory.GermConst.germ_constFn_origin R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← _root_.GlobalTheory.GermConst.germ_constFn_origin R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', _root_.GlobalTheory.GermConst.germ_constFn_origin]
  obtain ⟨z, hz0, hz1, hm⟩ := _root_.GlobalTheory.CoordsOrigin.coords_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.FormalOrigin.taylor_isRingHom _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, _root_.GlobalTheory.FormalOrigin.taylor_const _ R n (evO G) δ _ (fun i => hconst i r), GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := _root_.GlobalTheory.FormalOrigin.Extend.derivation_extends R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (_root_.GlobalTheory.spMap_fromSpecStalk_top_le_iff G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv R a), intDer dΩ,
    _root_.GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C R _ ‹_› n, ?_, (_root_.GlobalTheory.spMap_fromSpecStalk_top_le_iff G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, _root_.GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := _root_.GlobalTheory.TaylorInj.taylor_injective R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
