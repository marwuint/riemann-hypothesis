import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

section Tay

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : Type} [CommRing R] [Algebra ℂ R]

abbrev evT {W : Opens E} (R : Type) [CommRing R] [Algebra ℂ R] (p : E) (hp : p ∈ W) : R ⊗[ℂ] Hol W →ₐ[ℂ] R :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ R) ((Algebra.ofId ℂ R).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)

def IsTay {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} (N : ℕ) (t : I → R) {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀) : Prop :=
  ∀ (h : Hol W) (p : Tot Empty g) (hp : p ∈ W₀), evT R p hp (ρ h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)

end Tay

namespace Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R]

def shA {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →ₐ[ℂ] Hol (K.W k') :=
  Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)

theorem shA_apply {l : Λ} {k k' : K.K} (h : K.le l k' k) (x : Hol (K.W k)) : shA h x = sh h x := rfl

variable (K) in

structure DObj (η : Hol F.V →+* R) (M : Ideal R) : Type 1 where

  T : K.Obj
  [alg : Algebra R T.C]
  compat : ∀ f, algebraMap (Hol F.V) T.C f = algebraMap R T.C (η f)
  mem : ∀ d ∈ M, algebraMap R T.C d ∈ T.J

attribute [instance] DObj.alg

variable {η : Hol F.V →+* R} {M : Ideal R}

instance : Category (K.DObj η M) where
  Hom S S' := {f : S.T ⟶ S'.T // ∀ d, f.φ (algebraMap R S.T.C d) = algebraMap R S'.T.C d}
  id S := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f f' := ⟨f.1 ≫ f'.1, fun d ↦ by rw [comp_φ, f.2, f'.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f f' f'' := Subtype.ext (Category.assoc _ _ _)

variable (K η M) in

@[reducible] def OD : K.DObj η M ⥤ CommAlgCat.{0} R where
  obj S := CommAlgCat.of _ S.T.C
  map f := CommAlgCat.ofHom { (f.1.φ : _ →+* _) with commutes' := f.2 }

variable (K η M) in

def perZD (q : Λ →+ R) : Z1 (K.OD η M) :=
  ⟨fun _ S' f ↦ algebraMap R S'.T.C (q f.1.deg), fun S S' S'' f f' ↦ by
    change algebraMap _ S''.T.C (q (f.1.deg + f'.1.deg)) = f'.1.φ (algebraMap _ _ _) + algebraMap _ S''.T.C _
    rw [f'.2, map_add, map_add]⟩

variable (K η M) in

def perClD (q : Λ →+ R) : CatCoh.H1 (K.OD η M) := H1.mk _ (K.perZD η M q)

end Charts

section Theta

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R] {η : Hol F.V →+* R} {M : Ideal R}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}
  {D : Type} [CommRing D] {J : Ideal D}

structure IsOver (η : Hol F.V →+* R) (M : Ideal R) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) (J : Ideal D) (s' : X ⟶ Sp D)
    (π : D →+* B) (ι : D →+* R) : Prop where
  w : s' = s ≫ spMap π
  mem : ∀ d ∈ J, ι d ∈ M
  red : ∀ d, ι d - η (σ (π d)) ∈ M

variable (r : Real K s σ) (κ : DividedPowers J) {s' : X ⟶ Sp D} {π : D →+* B} {ι : D →+* R} (H : IsOver η M s σ J s' π ι)

def Real.objD (S : K.DObj η M) : Thick κ s' where
  B := S.T.C
  alg := ((algebraMap R S.T.C).comp ι).toAlgebra
  J := S.T.J
  δ := S.T.δ
  nil := letI := S.T.ratAlg; isPDNilpotent_of_rat _ S.T.nil
  dp := letI := S.T.ratAlg; isDPMorphism_of_rat κ S.T.δ _ fun d hd ↦ S.mem _ (H.mem d hd)
  B₀ := S.T.C ⧸ S.T.J
  π := Ideal.Quotient.mk S.T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r.x S.T.k
  w := by
    rw [H.w, Category.assoc, ← Category.assoc (r.x _), r.w, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    refine RingHom.ext fun d ↦ (Ideal.Quotient.eq.2 ?_).symm
    have := S.mem _ (H.red d)
    rw [map_sub, ← S.compat, ← S.T.ρ_cst] at this
    exact this

def Real.coefD : CoefMap ι (O κ s') (K.OD η M) where
  G :=
    { obj := r.objD κ H
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun d ↦ f.2 (ι d) }
          φ₀ := Ideal.quotientMap S'.T.J (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          comm := fun _ ↦ rfl
          dp := letI := S'.T.ratAlg; isDPMorphism_of_rat S.T.δ S'.T.δ (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          pt := r.analyticChartsRealization_comp_point_eq f.1 } }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (ι d) c).symm

end Theta

end GlobalTheory.AnPer
