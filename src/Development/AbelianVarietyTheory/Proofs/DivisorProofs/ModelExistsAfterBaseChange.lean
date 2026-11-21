import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqNsmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfObj
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.LevelRaise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem exists_enum (o : Obj D l b s) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      ∃ u : J → (Over.mk x ⟶ o.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient D M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨-, I, -⟩ := o.geom K x β.hom hβ.symm
  have hI : ∀ a b, I.ev M a = I.ev M b ↔ π a = π b := fun a b => by
    have h : I.ev M a = I.ev M (a - b) * I.ev M b := by rw [← I.add, sub_add_cancel]
    rw [hπ, h, mul_eq_right, I.ker M hM]
    rfl
  refine ⟨fun j => I.ev M (r j), fun i j hij => ?_, fun w => (I.onto M hM w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_finite_set (o : Obj D l b s) {M : ℕ} (hM : 0 < M) {K F : Type} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed F] (x : Sp K ⟶ S) :
    ∃ T : Set F, T.Finite ∧ ∀ L : IntermediateField K F, T ⊆ L →
      ∀ w : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ o.t.G, w ^ M = 1 →
        ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ o.t.G, spMap (algebraMap L F) ≫ q.left = w.left := by
  haveI := o.proper
  obtain ⟨J, _, hJ⟩ := exists_enum o hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose T hT using fun j => TorsionRat.exists_finset_over o.t.G x (u j)
  refine ⟨⋃ j, (T j : Set F), Set.finite_iUnion fun j => (T j).finite_toSet, fun L hL w hw => ?_⟩
  obtain ⟨j, rfl⟩ := (hu w).1 hw
  exact hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans hL)

end GlobalTheory.LevelRaise
