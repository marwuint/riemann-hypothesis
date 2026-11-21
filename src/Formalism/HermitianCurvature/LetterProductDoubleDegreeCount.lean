import Mathlib
import Formalism.HermitianCurvature.StatementLE
import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.StatementI
import Formalism.HermitianCurvature.StatementQ

namespace Formalism.FourierDecayAlt.C7

open Finset Matrix

open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

def LamInterlaces (k r : ℕ) (u : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin (k + 2 * r + 1),
    (i.val + 1 ≤ k → lam i < u (i.val + 1)) ∧ (i.val + 2 ≤ k → u (i.val + 2) < lam i)

def Between (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  min (u l) (u' l) < -Y ∧ -Y < max (u l) (u' l)

def LamSide : Prop :=
  ∀ (k r : ℕ) (u u' : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → Between u u' l Y →
    ∀ i : Fin (k + 2 * r + 1), (l ≤ i.val + 1 → lam i < min (u l) (u' l)) ∧
      (i.val + 1 < l → max (u l) (u' l) < lam i)

def RhoSide : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → Between u u' l Y →
    ∀ i ∈ Icc 1 (k - 1), (l ≤ i → ρ i < -Y) ∧ (i < l → -Y < ρ i)

def PSign : Prop :=
  ∀ (k r : ℕ) (u u' ρ : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → I.Interlaces k u u' ρ → Between u u' l Y →
    0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) ∧ 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y ∧
      |∏ s, (Y + lam s)| = (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s)

def principalHermitianLattice {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  B.beta D (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) F

def RootsOutJoint : Prop :=
  ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
    LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
    (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) → S.RootsOut

end

end Formalism.FourierDecayAlt.C7
