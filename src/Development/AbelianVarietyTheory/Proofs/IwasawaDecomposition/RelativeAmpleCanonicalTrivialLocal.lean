import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleSpreadOfPolarizedFiber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmple

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pull_ample_kTriv {S S' : Scheme.{0}} [IsAffine S] {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) :
    Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S)
    (fun _ => trivial) hA, kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem ample_kTriv_of_iso {S S' : Scheme.{0}} [IsAffine S'] {t : SAB H S} {u : SAB H S'} {j : S' ⟶ S} [IsIso j]
    (m : SABMap u t j) (hA : Out.RelAmple u.G u.PP.L) (hK : Out.KTriv u.G u.PP.L) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m n (g := inv j) (by simp)
  exact pull_ample_kTriv m' hA hK

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (hf : Function.Bijective f) :
    IsIso (spMap f) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isProper_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (hp : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback m.cart.1 hp

end GlobalTheory.PolLocal

namespace GlobalTheory.PolLocal

theorem algebraMap_fractionRing_bijective (O : Type) [CommRing O] [IsDomain O] (hf : IsField O) :
    Function.Bijective (algebraMap O (FractionRing O)) := by
  refine ⟨IsFractionRing.injective O (FractionRing O), fun z => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) z
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (nonZeroDivisors.ne_zero y.2)
  refine ⟨x * b, ?_⟩
  calc algebraMap O (FractionRing O) (x * b) = z * algebraMap O (FractionRing O) (y * b) := by
        rw [map_mul, map_mul, ← mul_assoc, ← hxy]
    _ = z := by rw [hb, map_one, mul_one]

end GlobalTheory.PolLocal
