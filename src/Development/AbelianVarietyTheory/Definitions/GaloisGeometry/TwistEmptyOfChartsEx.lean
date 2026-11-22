import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistedLevelExtension
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

namespace GlobalTheory.TwU.WildChar

end GlobalTheory.TwU.WildChar

namespace GlobalTheory.TwU.Rigid

end GlobalTheory.TwU.Rigid

noncomputable section

namespace GlobalTheory.TwU.Model

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.UG
open scoped TensorProduct

section CongBasic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) :
    IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end CongBasic

theorem sameCoset_equiv {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (P : rowSG Pr sel mu) :
    Equivalence (fun y y' : Sp X.E n => SameCoset sel mu cst P y y') where
  refl := fun y l => by
    rw [sub_self, Pi.zero_apply, mul_zero]
    exact ciIntAt_zero
  symm := fun {y y'} h l => by
    have h1 := ciIntAt_neg (h l)
    rwa [← mul_neg, ← Pi.neg_apply, neg_sub] at h1
  trans := fun {x y z} h h' l => by
    have h1 := (h l).add (h' l)
    rwa [← mul_add, ← Pi.add_apply, sub_add_sub_cancel] at h1

end GlobalTheory.TwU.Model

end
