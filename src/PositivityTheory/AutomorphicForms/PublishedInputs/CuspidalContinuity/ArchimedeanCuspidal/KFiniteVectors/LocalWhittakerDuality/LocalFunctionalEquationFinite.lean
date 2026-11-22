import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.K.GL2LocalData

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in

def em (h : GL (Fin 2) F) : GL (Fin 3) F :=
  if hd : (!![h.val 0 0, h.val 0 1, 0; h.val 1 0, h.val 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

def tinv {n : Type} [Fintype n] [DecidableEq n] (g : GL n F) : GL n F :=
  ⟨(g⁻¹ : GL n F).valᵀ, g.valᵀ, by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩

def w2 : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
def w3 : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

variable (F) in

def K2 : Set (GL (Fin 2) F) := (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))

def iw (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (s : ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F) : ℂ :=
  W (em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2) * mp p.1 (s - 3 / 2) * mp p.2.1 (2 * s - 1)

end D

section W

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

open Classical in
variable (E) in

def nsg (a : F) : ℂ := if ∃ t : Eˣ, Algebra.norm F (t : E) = a then 1 else -1

open Classical in

def rW (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d : F) (Φ : E → ℂ) (z : E) : ℂ :=
  if c = 0 then (χ (a * b * Algebra.norm F z) : ℂ) * nsg E a * ((modulus a : ℝ) : ℂ) * Φ (algebraMap F E a * z)
  else lam * nsg E (-c) * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) *
    ∫ u, (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) * Φ u ∂μE

variable (F E) in

def SBc (c : Eˣ →* ℂˣ) : Set (E → ℂ) :=
  {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
    ∀ u : Eˣ, Algebra.norm F (u : E) = 1 → ∀ x, Φ (x * u) = (((c u)⁻¹ : ℂˣ) : ℂ) * Φ x}

end W

section WF

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]

variable (E) in

def chE (χ : AddChar F Circle) : AddChar E Circle := χ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

variable (E) in

def lamE (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) : ℂ := gam χ 1 (1 / 2) * gam χ η (1 / 2) / gam (chE E χ) 1 (1 / 2)

end WF

def swapE {F : Type} [Field F] : (F × F) ≃ₐ[F] (F × F) := AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl)

section R

open Classical in

def rotR (θ : ℝ) : GL (Fin 2) ℝ :=
  if hd : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

def kR (θ : ℝ) (ε : Bool) : GL (Fin 2) ℝ := rotR θ * (if ε then dg2 1 (-1) else 1)

end R

end Ad3.K.GL2LocalData
