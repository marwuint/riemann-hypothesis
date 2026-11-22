import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueIsTransfer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RedCompatOfFiniteEtale

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrDeg

open GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem chainMap_comp {X Y Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z) :
    chainMap R (t ≫ t') = chainMap R t ≫ chainMap R t' := by
  have : simpMap R (t ≫ t') = simpMap R t ≫ simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_comp]
  exact CategoryTheory.Functor.map_comp _ _ _

theorem chainMap_add {X Y : Scheme.{0}} (t t' : freeSch R X ⟶ freeSch R Y) :
    chainMap R (t + t') = chainMap R t + chainMap R t' := by
  have : simpMap R (t + t') = simpMap R t + simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_add]
  exact (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map_add

theorem along_comp {X Y Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z)
    (x : H R (sch.obj Z) F n) : along R F n (t ≫ t') x = along R F n t (along R F n t' x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, chainMap_comp, Cochain.ofHom_comp]

theorem along_add {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (t t' : freeSch R X ⟶ freeSch R Y)
    (x : H R (sch.obj Y) F n) : along R F n (t + t') x = along R F n t x + along R F n t' x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine (congrArg CohomologyClass.mk (Cocycle.ext ?_)).trans (CohomologyClass.mk_add _ _)
  simp [zcomp, chainMap_add, Cochain.ofHom_add, Cochain.add_comp]

theorem along_nsmul_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (d : ℕ) (x : H R (sch.obj X) F n) :
    along R F n (d • 𝟙 (freeSch R X)) x = d • x := by
  induction d with
  | zero =>
    have h := along_add R F n (0 : freeSch R X ⟶ freeSch R X) 0 x
    rw [add_zero] at h
    rw [zero_smul, zero_smul]
    exact left_eq_add.1 h
  | succ d ih => rw [succ_nsmul, succ_nsmul, along_add, ih, along_id]

theorem generate_singleton_mem {U X : Scheme.{0}} (u : U ⟶ X) [Etale u] [Surjective u] :
    Sieve.generate (Presieve.singleton u) ∈ Scheme.etaleTopology X :=
  Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) u).2 ⟨(inferInstance : Surjective u).surj, inferInstance⟩)

theorem transfer_comp {Y X U : Scheme.{0}} {f : Y ⟶ X} {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) {t : freeSch R X ⟶ freeSch R Y} (ht : IsTransfer R f t) :
    t ≫ (free R).map (yoneda.map f) = d • 𝟙 _ := by
  refine free_hom_ext_of_covering R _ _ _ _ (generate_singleton_mem u) ?_
  rintro V v ⟨_, g, _, ⟨⟩, rfl⟩
  have hg := splitBy_baseChange hs g
  rw [← Category.assoc, ht.apply_of_splitBy R hg, Preadditive.sum_comp]
  have h1 : ∀ j, (free R).map (yoneda.map (g ≫ s j)) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (g ≫ u)) := fun j => by
    rw [← Functor.map_comp, ← Functor.map_comp, hg.1 j]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Preadditive.comp_nsmul, Category.comp_id]

theorem trH_pull {Y X U : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) :
    trH R f F n (pull R (sch.map f) F n x) = d • x := by
  rw [trH, ← along_free, ← along_comp,
    transfer_comp R hs (transfer_spec R (existsUnique_isTransfer R f).exists), along_nsmul_id]

end GlobalTheory.EtC.TrDeg

end
