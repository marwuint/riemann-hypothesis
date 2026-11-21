import Mathlib
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZs
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZp
import Formalism.LocalToGlobal.Columns.RowFormsNZw
import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

def v0N (r : ℕ) (c : Fin n → κ) : Matrix (Fin n) (Fin n) κ :=
  Matrix.of fun a b => if r ≤ a.val ∧ b.val < r then c b else 0

theorem nilpotentBlock_apply (r : ℕ) (c : Fin n → κ) (a b : Fin n) : v0N κ r c a b = if r ≤ a.val ∧ b.val < r then c b else 0 := rfl

variable {κ}

end StabComb

section Scal

variable {E : Type} [Field E] [NumberField E]

noncomputable instance unitTorsionFintype : Fintype (NumberField.Units.torsion E) := Fintype.ofFinite _

def diagonalUnitsHom (κ : Type) [CommRing κ] (n : ℕ) : (Fin n → κˣ) →* GL (Fin n) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem v0diag_val (κ : Type) [CommRing κ] (n : ℕ) (u : Fin n → κˣ) :
    ((diagonalUnitsHom κ n u : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((u i : κˣ) : κ) := rfl

end Scal

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem torsion_normOne (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (ζ : NumberField.Units.torsion E) :
    star ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) * ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have h1 := (NumberField.Units.mem_torsion E).mp ζ.2 w
  rw [← NumberField.InfinitePlace.norm_embedding_eq] at h1
  apply w.embedding.injective
  rw [map_mul, hconj, map_one, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h1]
  norm_num

def v0uE (ζ : NumberField.Units.torsion E) : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom (ζ : (𝓞 E)ˣ)

theorem torsionUnit_val (ζ : NumberField.Units.torsion E) : ((v0uE ζ : Eˣ) : E) = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) := rfl

def v0sc (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) : UF E n :=
  ⟨LinearEquiv.smulOfUnit (v0uE ζ), fun x y => by
    have hu := torsion_normOne hconj ζ
    show hStd E n ((v0uE ζ : Eˣ) • x) ((v0uE ζ : Eˣ) • y) = hStd E n x y
    rw [hStd_apply, hStd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, star_mul', torsionUnit_val]
    linear_combination (star (x i) * y i) * hu⟩

theorem torsionScalar_apply (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) (x : Sp E n) :
    (v0sc hconj n ζ).1 x = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) • x := rfl

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

end Formalism.L2.Col
