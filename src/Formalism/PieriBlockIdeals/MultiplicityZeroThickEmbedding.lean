import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.PieriBlockIdeals.MertensReciprocalElementary

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent.WorkedExample

open Formalism.CohomologicalDescent

def MwFlip : Prop :=
  ∀ (l : ℕ) (b h : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (h - (b + t - 1)) t κ (U.image fun u => h - u) = mwCount l b t κ U

def LinkageFlip : Prop :=
  ∀ (K : Type) [CommRing K] (N : ℕ) (U U' : Fin N → ℤ) (c c' h : ℤ),
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K)) →
    (∏ a, (Polynomial.X + Polynomial.C (((h - U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((h - U' a + c' : ℤ)) : K))

structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ

namespace Labels

variable {ι : Type} {N : ℕ}

def Refl (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) : Prop :=
  (∀ i, D.cc (D.cc i) = i) ∧ (∀ i, σ (D.cc i) = D.cc (σ i)) ∧ (∀ i, i ∈ D.Φ ∨ D.cc i ∈ D.Φ) ∧
  (∀ i a, D.U (D.cc i) a = (h : ℤ) - D.U i (Fin.rev a)) ∧
  (∀ i a, D.U' (D.cc i) a = (h : ℤ) - D.U' i (Fin.rev a)) ∧
  (∀ i, D.bot (D.cc i) = (h : ℤ) - (D.bot i + (t : ℤ) - 1))

def Linked (D : Labels ι N) (F : Type) [Field F] (t : ℕ) (cst : ι → ℤ) : Prop :=
  ∀ i ∈ D.Φ, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
    (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
    (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + cst i : ℤ)) : F))

def Carried (D : Labels ι N) (ep : ι → ι) (J : ι → Fin N → ℤ) (botJ : ι → ℤ) : Prop :=
  (ep = id ∨ ep = D.cc) ∧ (∀ i, J (ep i) = D.U' i) ∧ (∀ i, botJ (ep i) = D.bot i)

def mw (D : Labels ι N) (l t κ : ℕ) (i : ι) : ℕ :=
  mwCount l (D.bot i) t κ (Finset.univ.image (D.U i))

end Labels

def ShapeAt {ι : Type} (k j t q : ℕ) (D : Labels ι (k + j + t + q)) (τ : ι) : Prop :=
  (∀ a, 0 ≤ D.U τ a) ∧ ∑ a, D.U τ a = ∑ a, D.U' τ a ∧
  ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
    D.U τ a = D.bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)

def DepthBound {ι : Type} (k j t q l h : ℕ) (D : Labels ι (k + j + t + q)) (σ : Equiv.Perm ι)
    (τ : ι) : Prop :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (D.U τ a - D.U' τ a) ≤
    (q : ℤ) * h +
      ((l : ℤ) * (D.mw l t (h / (l - 1)) (σ τ) : ℤ) + (D.mw l t (h / (l - 1)) τ : ℤ)) *
        ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))

def MwLetters : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ), D.Refl σ h t →
    ∀ (l κ : ℕ) (i : ι), D.mw l t κ (D.cc i) = D.mw l t κ i

def LinkedAll : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (F : Type) [Field F]
    (cst : ι → ℤ), D.Refl σ h t → D.Linked F t cst →
    ∀ i, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
      (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + 0 : ℤ)) : F))

def WEOrientLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F L : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O)
    [IsAdicComplete I O] (W : FrobeniusPeriodChange.WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι)
    (ζ : O) (em : O →+* L) (jj : ℕ → PowerSeries O →+* PowerSeries L),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    FrobeniusPeriodChange.NInputs W σ l h u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap I ζ em jj →
    ShapeAt k j t q D τ →
    DepthBound k j t q l h D σ τ

end Formalism.CohomologicalDescent.WorkedExample
