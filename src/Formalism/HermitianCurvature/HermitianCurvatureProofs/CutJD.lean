import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GlobCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d : ℝ) : Prop :=
  ∀ Tm ∈ Θ, B.CkOn ⊤ (B.GV k r) Tm.coef ∧ B.CkOn ⊤ (B.GV k r) Tm.coefAdj ∧
    ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r,
        ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ d ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ d

def nDim (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def bddHat (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ X ∈ MA.hatSet P L, x = b * X}

def JDHatBdd : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 ≤ P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L)

def JDJComm : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (d A : ℝ), 0 ≤ d →
      B.SmoothCoef (B.GPos (T v).base) Θ → B.Commutes (T v).base (B.GPos (T v).base) Θ → GlobCoef Θ d →
      Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        B.JF (T v).base (B.opApply Θ F) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
          ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            B.opApply Θ (B.JF (T v).base F) (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x)

def JDCCLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ),
    0 ≤ d → GlobCoef Θ d → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC A m F) →
      B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ ∀ m : ℕ, B.InCC (A - d) m (B.opApply Θ F)

def TransferSquareIntegrable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ A : ℝ, Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ π, MeasureTheory.Integrable
          (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF (T v).base F) π) q‖ ^ 2) (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

def BoundedOperatorsSquareIntegrable : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ u : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT)) →
      ∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (MA.actA P b u π) q‖ ^ 2) (MA.mu0 P.r P.TT)

end

end Formalism.FourierDecayAlt.P.CutMP
