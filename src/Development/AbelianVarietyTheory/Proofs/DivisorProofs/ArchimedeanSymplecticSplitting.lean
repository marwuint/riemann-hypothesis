import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.SympNormal

open GlobalTheory.ArchUniq Module

section Gen

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def omegaL {P : V → V → ℝ} (h : IsPairing P) : (V × V) →ₗ[ℝ] (V × V) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (omega P)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)

@[simp] theorem omegaL_apply {P : V → V → ℝ} (h : IsPairing P) (w w' : V × V) :
    omegaL h w w' = omega P w w' := rfl

end Gen

end GlobalTheory.SympNormal
