import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.AltPullApply
import Development.AbelianVarietyTheory.Definitions.Divisors.CircleAsphGNontrivial

noncomputable section

namespace GlobalTheory.KS

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

abbrev pow (A : Over S) (m : ℕ) : Over S := ∏ᶜ fun _ : Fin m => A

abbrev pr (A : Over S) {m : ℕ} (i : Fin m) : pow A m ⟶ A := Pi.π (fun _ : Fin m => A) i

def matEnd {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : pow A m ⟶ pow A m :=
  Pi.lift fun i => (List.ofFn fun j => pr A j ≫ act.act (M i j)).prod

def powMap {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (h : φ ≫ A.hom = A'.hom ≫ f)
    (m : ℕ) : (pow A' m).left ⟶ (pow A m).left :=
  (Pi.lift (fun i => Over.homMk ((pr A' i).left ≫ φ) (by
    rw [Category.assoc, h, ← Category.assoc, Over.w]; rfl)) : Over.mk ((pow A' m).hom ≫ f) ⟶ pow A m).left

variable {B B' : Scheme.{0}}

abbrev ksBC (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : Scheme.{0} := pullback ((pow A m).hom ≫ p) b

def matBC {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (M : Matrix (Fin m) (Fin m) O) :
    ksBC A m p b ⟶ ksBC A m p b :=
  pullback.map _ _ _ _ (matEnd act M).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, Over.w]) (by simp)

variable (l : ℕ) [Fact l.Prime] (E : Type) [CommRing E] [Algebra ℚ_[l] E]

abbrev HE (Y : Scheme.{0}) (n : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n 0

def pullE {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : HE l E Y' n →ₗ[E] HE l E Y n :=
  (pullHQ l (sch.map u) n 0).baseChange E

variable {E}

def op {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n : ℤ) : Module.End E (HE l E (ksBC A m p b) n) :=
  ε.sum fun M c => c • pullE l E (matBC act p b M) n

def galE (E : Type) [CommRing E] [Algebra ℚ_[l] E] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (n : ℤ) (σ : Ω ≃ₐ[k] Ω) : Module.End E (HE l E (GlobalTheory.Et.geom Ω q) n) :=
  pullE l E (GlobalTheory.Et.galMap Ω q σ) n

variable (E) in

abbrev HEt (Y : Scheme.{0}) (n t : ℤ) : Type 1 := E ⊗[ℚ_[l]] HQ l (sch.obj Y) n t

variable (E) in

def pullEt {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n t : ℤ) : HEt l E Y' n t →ₗ[E] HEt l E Y n t :=
  (pullHQ l (sch.map u) n t).baseChange E

def opT {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (ε : Matrix (Fin m) (Fin m) O →₀ E)
    (n t : ℤ) : Module.End E (HEt l E (ksBC A m p b) n t) :=
  ε.sum fun M c => c • pullEt l E (matBC act p b M) n t

variable (E) in
theorem pullEt_zero {Y Y' : Scheme.{0}} (u : Y ⟶ Y') (n : ℤ) : pullEt l E u n 0 = pullE l E u n := rfl

@[simp] theorem opT_zero_comb {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (p : S ⟶ B) (b : B' ⟶ B) (n t : ℤ) :
    opT l act p b (0 : Matrix (Fin m) (Fin m) O →₀ E) n t = 0 := by
  simp [opT]

end GlobalTheory.KS
