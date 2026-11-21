import Mathlib

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

open Classical

def vl (l : ℕ) (n : ℤ) : ℕ := padicValInt l n

def IlInd (l : ℕ) (xm xp mB : ℤ) : ℝ :=
  if ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB then 1 else 0

def d0 (l : ℕ) (D : ℤ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)}

def labelLHS (l k t : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (∑ ct ∈ Finset.Icc xm xp, (k : ℝ) * (vl l (ct - mB) : ℝ)) +
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)

def labelSumBound (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))

def LabelSum : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → 0 ≤ mB → mB < xm → xm ≤ xp →
    xp ≤ (h : ℤ) → h < l ^ 2 → l ≤ 2 * h →
    labelLHS l k t i xm xp mB ≤ labelSumBound l k t h i xm xp mB

def Linkage : Prop :=
  ∀ (l : ℕ) (K : Type) [Field K] [CharP K l] (N : ℕ) (U U' : Fin N → ℤ) (c : ℤ), l.Prime →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    Multiset.map (fun a => ((U a : ℤ) : ZMod l)) Finset.univ.val =
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val

def mwCount (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) : ℕ :=
  ((U.filter (fun u => u ∉ Finset.Icc b (b + t - 1))).filter
    (fun u => ∃ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ), x ≡ u [ZMOD (l : ℤ)])).card

def KapSum : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ) (kap : Fin t → ℤ), 0 < l → t + 2 * κ < l →
    (∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ U) → (∀ s, |kap s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kap s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun u : ℤ => (u : ZMod l)) U.val →
    |∑ s, kap s| ≤ (mwCount l b t κ U : ℤ) * ((t : ℤ) + 2 * κ)

def WEArith : Prop :=
  ∀ (k j t q l h κ mw mwp : ℕ) (U U' : Fin (k + j + t + q) → ℤ) (kc kp : ℤ),
    StrictAnti U → StrictAnti U' → (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) →
    ∑ a, U a = ∑ a, U' a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * kp - kc →
    |kc| ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) → |kp| ≤ (mwp : ℤ) * ((t : ℤ) + 2 * κ) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h + ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ)

def GatedSum : Prop :=
  ∀ (D h : ℕ) (L A k : ℝ) (P : Finset ℕ), 1 ≤ D → D ≤ h → 0 ≤ A → 0 ≤ k → (h : ℝ) < L ^ 2 →
    1 ≤ L → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, (if ((d0 l D : ℕ) : ℤ) < (D : ℤ) then min k (A / (d0 l D : ℝ)) else 0) *
        Real.log (l : ℝ) ≤
      A * (1 + Real.log (h : ℝ)) * Real.log (h : ℝ)

end Formalism.CohomologicalDescent
