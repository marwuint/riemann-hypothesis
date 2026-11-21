import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable (ι) in

abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)

def IsSec (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) : Prop :=
  ∃ a : K → ℕ, IsMultiHomog s a ∧ (∀ k, (a k : ℤ) = A.a k) ∧ s ∉ P

open Classical in

def horizPart (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ W ∈ (divSupp_finite P s).toFinset.filter (fun W => IsHorizontal W),
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L

open Classical in

def vertPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ V ∈ (divSupp_finite P s).toFinset.filter (fun V => ¬ IsHorizontal V),
    (multAt (P ⊔ Ideal.span {s}) V : ℝ) * (geoNum n V (degs L) : ℝ) * Real.log (charOf V)

def intPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ :=
  ptsIntegral P (pots L) (logNorm A s)

def rhsR (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : ℝ :=
  horizPart I P L s + vertPart P L s - intPart P L A s

def IsFamilyOn (I : Family ι) (good : ℕ → Prop) : Prop :=
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)),
      good n → IsArithVar P n → AllSmooth L → I P n (L ∘ σ) = I P n L) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
      good n → IsArithVar P n → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      I P n (Function.update L j (A.tensor B)) =
        I P n (Function.update L j A) + I P n (Function.update L j B)) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin (n + 1) → HermLine ι) (s : MRing ι),
      good (n + 1) → IsArithVar P (n + 1) → AllSmooth L → IsSec P (L (Fin.last n)) s →
      I P (n + 1) L = rhsR I P (Fin.init L) (L (Fin.last n)) s)

def IsFamily (I : Family ι) : Prop := IsFamilyOn I fun _ => True

end Objects

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
