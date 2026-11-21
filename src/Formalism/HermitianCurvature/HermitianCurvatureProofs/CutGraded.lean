import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName

open Formalism.FourierDecayAlt MeasureTheory NumberField

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.Gr

noncomputable section

section cls

variable {r : ℕ} {TT : ℝ}

def smM (m : ℕ∞) : WithTop ℕ∞ := ((m : ℕ∞) : WithTop ℕ∞)

def smSubM (r : ℕ) (TT : ℝ) (m : ℕ∞) : Subalgebra ℂ (MA.Qp r TT → ℂ) where
  carrier := {f | ContDiffOn ℝ (smM m) (MA.ext f) (MA.Qset r TT)}
  mul_mem' {f g} hf hg := (hf.mul hg).congr fun x hx => by simp [MA.ext, hx]
  add_mem' {f g} hf hg := (hf.add hg).congr fun x hx => by simp [MA.ext, hx]
  algebraMap_mem' z := (contDiffOn_const (c := z)).congr fun x hx => by simp [MA.ext, hx]

theorem smSubM_top : smSubM r TT ⊤ = MA.smSub r TT := rfl

end cls

section ord

variable {r : ℕ} {TT : ℝ}

inductive Fac (r : ℕ) (TT : ℝ) : Type
  | mul (f : MA.SmQ r TT) : Fac r TT
  | eul (v : M.Var r) : Fac r TT

def Fac.op : Fac r TT → (MA.anQ r TT).Op
  | .mul f => (MA.anQ r TT).mulOp f
  | .eul v => MA.eulerQ v

end ord

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FFlM {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (m : ℕ∞) (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : Set (Q.Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | (∀ g₀ ∈ Q.Glev k r i ∩ Dm, ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (smM m) F U ∧ ∀ g ∈ U, g ∈ Q.Glev k r i → J g = F g) ∧
    Q.LeftEq k r z i Dm J ∧ Q.RightEq k r z' i Dm J ∧
    ∀ g ∈ Q.Glev k r i ∩ Dm, ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h'))}

theorem fflM_top {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (Dm : Set (Q.Mx k r)) : FFlM ⊤ k r z z' π π' i Dm = Q.FFl k r z z' π π' i Dm := rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gr
