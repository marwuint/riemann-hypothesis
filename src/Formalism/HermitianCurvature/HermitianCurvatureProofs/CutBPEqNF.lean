import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem fpmSh_eq_fpm (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (p₀ : ℕ) :
    fpmSh q f A p₀ = TBBx4.fpm q (fun g => (f g).comp (A g)) (fun _ => ContinuousLinearMap.id ℂ Wq') p₀ := by
  first
  | rfl
  | (unfold fpmSh; rfl)
  | unfold fpmSh

theorem inCC_compSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} {A₀ : ℝ} {d : ℕ} (hf : ∀ m : ℕ, B.InCC A₀ m f) (hA : PolyOp d A) :
    ∀ m : ℕ, B.InCC (A₀ - d) m (fun g => (f g).comp (A g)) := by
  intro m
  have h := shifted_decay P Wp Wq Wq' u u' q f A A₀ d 0 hf hA m
  simp only [mul_zero, Nat.cast_zero, sub_zero] at h
  first
  | exact h
  | (convert h using 2; rw [fpmSh_eq_fpm]; simp [TBBx4.fpm])
  | (convert h using 2; rw [fpmSh_eq_fpm]; unfold TBBx4.fpm)

end sh

end

end Formalism.FourierDecayAlt.P.CutBPEq
