import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

end GlobalTheory.HTPres
