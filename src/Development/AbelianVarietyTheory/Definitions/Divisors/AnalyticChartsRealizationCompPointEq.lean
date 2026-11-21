import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem isDPMorphism_of_rat {C C' : Type} [CommRing C] [CommRing C'] [Algebra ℚ C'] {J : Ideal C} {J' : Ideal C'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : C →+* C') (h : ∀ c ∈ J, φ c ∈ J') : IsDPMorphism δ δ' φ := by
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 h, fun n _ a ha ↦ ?_⟩
  have hu : IsUnit ((n.factorial : ℕ) : C') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ C')
    simpa using this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h a ha), ← map_pow, ← δ.factorial_mul_dpow_eq_pow ha, map_mul, map_natCast]

theorem isPDNilpotent_of_rat {C : Type} [CommRing C] [Algebra ℚ C] {J : Ideal C} (δ : DividedPowers J)
    (h : IsNilpotent J) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J) →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J ^ (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl
      have hp : p.2 ∈ J := hl p (by simp)
      simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
      refine Ideal.mul_mem_mul ?_ (ih fun q hq ↦ hl q (by simp [hq]))
      have hu : IsUnit ((p.1.factorial : ℕ) : C) := by
        have := (IsUnit.mk0 (p.1.factorial : ℚ) (by exact_mod_cast p.1.factorial_ne_zero)).map (algebraMap ℚ C)
        simpa using this
      rw [← Ideal.unit_mul_mem_iff_mem _ hu, δ.factorial_mul_dpow_eq_pow hp]
      exact Ideal.pow_mem_pow hp _
  refine ⟨N, fun l hl hs ↦ ?_⟩
  have := Ideal.pow_le_pow_right hs (key l hl)
  rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}}

@[reducible] def Charts.Obj.ratAlg {K : Charts F} (T : K.Obj) : Algebra ℚ T.C :=
  ((algebraMap (Hol F.V) T.C).comp ((algebraMap ℂ (Hol F.V)).comp (algebraMap ℚ ℂ))).toAlgebra

open Classical in

def Charts.Obj.δ {K : Charts F} (T : K.Obj) : DividedPowers T.J :=
  letI := T.ratAlg
  RatAlgebra.dividedPowers T.J

structure Unif (F : Fam I g Λ) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) where

  E : Tot I g → (Sp ℂ ⟶ X)
  w : ∀ (p : Tot I g) (hp : p.1 ∈ F.V), E p ≫ s = spMap ((Hol.ev p.1 hp).toRingHom.comp σ)
  per : ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → E (F.shift l p) = E p
  hol : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ E p ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun p ↦ valAt' (E p) U f) {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ E p ⁻¹ᵁ U}

def Unif.Based {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) : Prop :=
  ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z ∈ F.V, ⊤ ≤ u.E (z, 0) ⁻¹ᵁ U

structure Real (K : Charts F) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) where

  x : ∀ k, Sp (Hol (K.W k)) ⟶ X
  w : ∀ k, x k ≫ s = spMap ((K.cst k).comp σ)
  compat : ∀ {l k k'} (h : K.le l k' k), spMap (Charts.sh h) ≫ x k = x k'

namespace Real

variable {K : Charts F} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ)

def IsFor (u : Unif F s σ) : Prop :=
  ∀ k (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ r.x k = u.E p

def obj (T : K.Obj) : Thick (dp0 B) s where
  B := T.C
  alg := ((algebraMap (Hol F.V) T.C).comp σ).toAlgebra
  J := T.J
  δ := T.δ
  nil := letI := T.ratAlg; isPDNilpotent_of_rat _ T.nil
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := T.C ⧸ T.J
  π := Ideal.Quotient.mk T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r.x T.k
  w := by
    rw [Category.assoc, r.w, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun b ↦ congrArg (Ideal.Quotient.mk T.J) (T.ρ_cst (σ b))

theorem analyticChartsRealization_comp_point_eq {T T' : K.Obj} (f : T ⟶ T') :
    spMap (Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem) ≫ spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r.x T.k =
      spMap ((Ideal.Quotient.mk T'.J).comp T'.ρ) ≫ r.x T'.k := by
  have e : (Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem).comp ((Ideal.Quotient.mk T.J).comp T.ρ) =
      ((Ideal.Quotient.mk T'.J).comp T'.ρ).comp (Charts.sh (Charts.Hom.le f)) :=
    RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (f.close.sub_mem h)
  rw [← r.compat (Charts.Hom.le f), ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, e]

def functor : K.Obj ⥤ Thick (dp0 B) s where
  obj := r.obj
  map {T T'} f :=
    { φ := { (f.φ : T.C →+* T'.C) with commutes' := fun b ↦ f.φ.commutes (σ b) }
      φ₀ := Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem
      comm := fun _ ↦ rfl
      dp := letI := T'.ratAlg; isDPMorphism_of_rat T.δ T'.δ (f.φ : T.C →+* T'.C) f.mem
      pt := r.analyticChartsRealization_comp_point_eq f }

def coef : CoefMap σ (O (dp0 B) s) K.Oc where
  G := r.functor
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.C) (σ b) c).symm

end Real

def IsPeriod {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (c : FirstDeRham s) (per : Λ →+ Hol F.V) : Prop :=
  ∀ (K : Charts F) (r : Real K s σ), r.IsFor u → r.coef.pull1 c = K.perCl per

namespace MulGrp

open ReciprocityTheory.ChartRestriction.G.TB.ValAt Polynomial

variable (I) in

def fam : Fam I 1 ℤ where
  V := ⊤
  τ := { toFun l := fun _ _ ↦ l * (2 * Real.pi * Complex.I)
         map_zero' := by funext _ _; simp
         map_add' l m := by funext _ _; simp [add_mul] }
  hol _ := analyticOnNhd_const

variable (σ : B →+* Hol (fam I).V)

end MulGrp

end GlobalTheory.AnPer
