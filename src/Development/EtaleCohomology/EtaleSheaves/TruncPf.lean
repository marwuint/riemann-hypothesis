import Development.EtaleCohomology.EtaleSheaves.FiltPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncPf

def TruncBij : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (n : ℤ),
  (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p)) → ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m)

variable (R : Type) [CommRing R] (F : Shv R)

theorem toHom_inj {K : Cx R} (m : ℤ) {x y : HK R K F m}
    (h : CohomologyClass.toHom x = CohomologyClass.toHom y) : x = y := by
  apply CohomologyClass.homAddEquiv.injective
  simpa only [CohomologyClass.homAddEquiv_apply] using h

theorem pull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (m : ℤ) (x : HK R M F m) :
    HK.pull R (f ≫ g) F m x = HK.pull R f F m (HK.pull R g F m x) := by
  apply toHom_inj
  simp only [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom, Functor.map_comp, Category.assoc]

theorem pull_id {K : Cx R} (m : ℤ) (x : HK R K F m) : HK.pull R (𝟙 K) F m x = x := by
  apply toHom_inj
  rw [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

theorem pull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (m : ℤ) : Function.Bijective (HK.pull R f F m) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨HK.pull R (inv f) F m y, ?_⟩⟩
  · have := congrArg (HK.pull R (inv f) F m) hxy
    simpa only [← pull_comp, IsIso.inv_hom_id, pull_id] using this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem subsingleton_of_isZero {K : Cx R} (hK : IsZero K) (m : ℤ) : Subsingleton (HK R K F m) := by
  constructor
  intro x y
  apply toHom_inj
  exact (Functor.map_isZero (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)) hK).eq_of_src _ _

theorem relK_of_isZero {K L : Cx R} (f : K ⟶ L) (n : ℤ) (hK : IsZero K) (hL : IsZero L) : RelK R F n f :=
  ⟨fun m _ _ => ⟨0, (subsingleton_of_isZero R F hK m).elim _ _⟩,
    fun _ _ _ => (subsingleton_of_isZero R F hL n).elim _ _⟩

theorem relK_of_square {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L' F m),
      HK.pull R f F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f' F m z) := by
    intro m z
    rw [← pull_comp, ← pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨y', rfl⟩ := (hg m (by omega)).2 y
    obtain ⟨z, rfl⟩ := hf'.1 m hm y'
    exact ⟨_, key m z⟩
  · obtain ⟨w1, rfl⟩ := (hh n le_rfl).2 x1
    obtain ⟨w2, rfl⟩ := (hh n le_rfl).2 x2
    rw [key, key] at hx
    rw [hf'.2 ((hg n le_rfl).1 hx)]

end LateralTheory.E.TruncPf

