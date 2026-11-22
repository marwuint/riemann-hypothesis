import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.NCyc

structure StrictLoc (X : Scheme.{0}) (x : X) where

  A : Type
  [ring : CommRing A]
  [isLocal : IsLocalRing A]

  φ : X.presheaf.stalk x →+* A
  isStrictHenselisation : IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ

attribute [instance] StrictLoc.ring StrictLoc.isLocal

namespace StrictLoc

variable {X : Scheme.{0}} {x : X}

abbrev scheme (L : StrictLoc X x) : Scheme.{0} := Spec (CommRingCat.of L.A)

def toX (L : StrictLoc X x) : L.scheme ⟶ X :=
  Spec.map (CommRingCat.ofHom L.φ) ≫ X.fromSpecStalk x

theorem henselian (L : StrictLoc X x) : HenselianLocalRing L.A := L.isStrictHenselisation.1

theorem isSepClosed (L : StrictLoc X x) : IsSepClosed (ResidueField L.A) := L.isStrictHenselisation.2.1

end StrictLoc

def SpecialPoint {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Type :=
  {x : X // p x = closedPoint O}

section Milnor

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {O : Type} [CommRing O] (K : Type) [Field K] [Algebra O K]

abbrev gfib {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) : Scheme.{0} := GlobalTheory.Et.fibre g (algebraMap O K)

def gfibAut {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) : gfib K g ⟶ gfib K g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3
    ext a
    simp)

@[reassoc] theorem gfibAut_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) :
    gfibAut K g σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem gfibAut_snd {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) :
    gfibAut K g σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K)) :=
  pullback.lift_snd _ _ _

def gfibMap {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)} (u : T ⟶ T')
    (hu : u ≫ g' = g) : gfib K g ⟶ gfib K g' :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

@[reassoc] theorem gfibMap_fst {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) : gfibMap K u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

@[reassoc] theorem gfibMap_snd {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) : gfibMap K u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

end Milnor

end GlobalTheory.NCyc

namespace GlobalTheory.NCyc

section Stalk

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (K : Type) [Field K] [Algebra O K]
variable [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

abbrev milnor [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {x : X} (L : StrictLoc X x) : Scheme.{0} := gfib K (L.toX ≫ p)

def stalk [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Type 1 := GlobalTheory.Et.H R n (milnor K p L)

instance (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : AddCommGroup (stalk R K p n x L) :=
  inferInstanceAs (AddCommGroup (GlobalTheory.Et.H R n (milnor K p L)))

instance (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Module R (stalk R K p n x L) :=
  inferInstanceAs (Module R (GlobalTheory.Et.H R n (milnor K p L)))

variable {p} {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)}

variable (p)

abbrev pushMilnor [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {X' : Scheme.{0}} (π : X' ⟶ X) {x : X} (L : StrictLoc X x) : Scheme.{0} :=
  gfib K (pullback.snd π L.toX ≫ L.toX ≫ p)

def pushStalk [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Type 1 :=
  GlobalTheory.Et.H R n (pushMilnor K p π L)

instance {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    AddCommGroup (pushStalk R K p π n x L) := inferInstanceAs (AddCommGroup (GlobalTheory.Et.H R n (pushMilnor K p π L)))

instance {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    Module R (pushStalk R K p π n x L) := inferInstanceAs (Module R (GlobalTheory.Et.H R n (pushMilnor K p π L)))

end Stalk

end GlobalTheory.NCyc

namespace GlobalTheory.NCyc

theorem henselian_powerSeries_complex : HenselianLocalRing (PowerSeries ℂ) := by
  have : IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  exact { is_henselian := fun f hf a h1 h2 =>
    HenselianRing.is_henselian (I := maximalIdeal (PowerSeries ℂ)) f hf a h1 (h2.map _) }

theorem isSepClosed_residueField_powerSeries_complex : IsSepClosed (ResidueField (PowerSeries ℂ)) := by
  let f : ℂ →+* ResidueField (PowerSeries ℂ) := (residue _).comp PowerSeries.C
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    refine ⟨PowerSeries.constantCoeff g, ?_⟩
    simp only [f, RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff]
    simp
  haveI : IsAlgClosed (ResidueField (PowerSeries ℂ)) :=
    IsAlgClosed.of_ringEquiv ℂ _ (RingEquiv.ofBijective f ⟨f.injective, hs⟩)
  infer_instance

attribute [local instance] henselian_powerSeries_complex isSepClosed_residueField_powerSeries_complex

theorem faithfulSMul_powerSeries_complex :
    FaithfulSMul (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))]
  exact (algebraMap (FractionRing (PowerSeries ℂ)) _).injective.comp (IsFractionRing.injective _ _)

theorem isAlgebraic_powerSeries_complex :
    Algebra.IsAlgebraic (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) :=
  ⟨fun x => (IsFractionRing.isAlgebraic_iff (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) _).2
    (Algebra.IsAlgebraic.isAlgebraic x)⟩

attribute [local instance] faithfulSMul_powerSeries_complex isAlgebraic_powerSeries_complex

end GlobalTheory.NCyc
