import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

section Places

variable (F : Type) [Field F] [NumberField F]

abbrev Pl : Type := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

variable {F}

def Kp : Pl F → Type
  | .inl w => w.Completion
  | .inr v => v.adicCompletion F

instance (u : Pl F) : Field (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (Field w.Completion)
  | .inr v => inferInstanceAs (Field (v.adicCompletion F))

instance (u : Pl F) : Algebra F (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (Algebra F w.Completion)
  | .inr v => inferInstanceAs (Algebra F (v.adicCompletion F))

instance (u : Pl F) : TopologicalSpace (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (TopologicalSpace w.Completion)
  | .inr v => inferInstanceAs (TopologicalSpace (v.adicCompletion F))

open Classical in

def inc : (u : Pl F) → Kp u → AF F
  | .inl w => fun y => pairA F (Pi.single w y) 0
  | .inr v => fun y => pairA F 0 (singleV F v y)

instance (u : Pl F) : IsTopologicalRing (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (IsTopologicalRing w.Completion)
  | .inr v => inferInstanceAs (IsTopologicalRing (v.adicCompletion F))

instance (u : Pl F) : T2Space (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (T2Space w.Completion)
  | .inr v => inferInstanceAs (T2Space (v.adicCompletion F))

instance (u : Pl F) : IsTopologicalDivisionRing (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (IsTopologicalDivisionRing w.Completion)
  | .inr v => inferInstanceAs (IsTopologicalDivisionRing (v.adicCompletion F))

end Places

section Quat

variable {F : Type} [Field F]

abbrev Q (d β : F) (R : Type) [CommRing R] [Algebra F R] : Type :=
  ℍ[R, algebraMap F R d, 0, algebraMap F R β]

variable {d β : F} {R : Type} [CommRing R] [Algebra F R]

def qn (x : Q d β R) : R :=
  x.re ^ 2 - algebraMap F R d * x.imI ^ 2 - algebraMap F R β * x.imJ ^ 2 +
    algebraMap F R d * algebraMap F R β * x.imK ^ 2

def qmap {R' : Type} [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') : Q d β R →+* Q d β R' where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def rat : Q d β F →+* Q d β R := qmap (Algebra.ofId F R)

section Top

variable [TopologicalSpace R]

instance qTop : TopologicalSpace (Q d β R) :=
  TopologicalSpace.induced (QuaternionAlgebra.equivProd _ _ _) inferInstance

theorem continuous_re : Continuous fun x : Q d β R => x.re := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.fst
theorem continuous_imI : Continuous fun x : Q d β R => x.imI := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.fst
theorem continuous_imJ : Continuous fun x : Q d β R => x.imJ := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.snd.fst
theorem continuous_imK : Continuous fun x : Q d β R => x.imK := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.snd.snd

theorem continuous_q_iff {X : Type*} [TopologicalSpace X] {f : X → Q d β R} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  constructor
  · intro hf
    exact ⟨continuous_re.comp hf, continuous_imI.comp hf, continuous_imJ.comp hf, continuous_imK.comp hf⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact continuous_induced_rng.2 (h1.prodMk (h2.prodMk (h3.prodMk h4)))

instance [IsTopologicalRing R] : IsTopologicalRing (Q d β R) where
  continuous_add := by
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · first
      | exact (continuous_re.comp continuous_fst).add (continuous_re.comp continuous_snd)
      | exact (continuous_imI.comp continuous_fst).add (continuous_imI.comp continuous_snd)
      | exact (continuous_imJ.comp continuous_fst).add (continuous_imJ.comp continuous_snd)
      | exact (continuous_imK.comp continuous_fst).add (continuous_imK.comp continuous_snd)
  continuous_mul := by
    have a1 := (continuous_re (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a2 := (continuous_imI (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a3 := (continuous_imJ (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a4 := (continuous_imK (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have b1 := (continuous_re (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b2 := (continuous_imI (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b3 := (continuous_imJ (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b4 := (continuous_imK (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    simp only [Function.comp_def] at a1 a2 a3 a4 b1 b2 b3 b4
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> fun_prop
  continuous_neg := by
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg]
    exact ⟨continuous_re.neg, continuous_imI.neg, continuous_imJ.neg, continuous_imK.neg⟩

end Top

end Quat

section QuatAlg

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

theorem mul_star_eq (x : Q d β R) : x * star x = algebraMap R (Q d β R) (qn x) := by
  ext <;> simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, qn] <;> ring

theorem star_mul_eq (x : Q d β R) : star x * x = algebraMap R (Q d β R) (qn x) := by
  ext <;> simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, qn] <;> ring

end QuatAlg

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def J2 (E : Type) [Field E] [Algebra F E] (β : F) : Matrix (Fin 2) (Fin 2) E :=
  !![1, 0; 0, -algebraMap F E β]

end Two

end GlobalTheory.CompanionTheory.PlaneSA
