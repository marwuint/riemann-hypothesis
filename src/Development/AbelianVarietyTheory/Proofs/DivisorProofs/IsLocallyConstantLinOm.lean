import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCoinvQuotEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter

noncomputable section

open GlobalTheory.WeilM GlobalTheory.LinPair MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace GlobalTheory.HypPair

section Char

variable {k E : Type} [Field k] [Field E] [Algebra k E] {c : E →ₐ[k] E}

def slU (x y z t : E) (hx : c x = x) (hy : c y = y) (hz : c z = z) (ht : c t = t) (h : x * t - y * z = 1) :
    UG c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![x, y; z, t] (by rw [det_fin_two_of, h]; exact one_ne_zero), by
    show (!![x, y; z, t])ᵀ * _ * (!![x, y; z, t]).map c = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hx, hy, hz, ht, vecMul, dotProduct] <;>
      first | ring1 | linear_combination h | linear_combination -h⟩

theorem slU_val (x y z t : E) (hx : c x = x) (hy : c y = y) (hz : c z = z) (ht : c t = t) (h : x * t - y * z = 1) :
    ((slU x y z t hx hy hz ht h : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = !![x, y; z, t] := rfl

end Char

section Schr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {ψ : AddChar k ℂ} {κ : Type} [Fintype κ]

theorem schr_mem (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    schr ψ w φ ∈ SB (κ → k) := by
  have := nonarch_field k
  exact ⟨((isLocallyConstant_addChar ψ hψ).comp_continuous
      ((continuous_id.dotProduct continuous_const).add continuous_const)).mul
    (hφ.1.comp_continuous (continuous_id.add continuous_const)),
    (hφ.2.comp_homeomorph (Homeomorph.addRight w.1)).mul_left⟩

def schrS (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) : Module.End ℂ (SB (κ → k)) :=
  (GlobalTheory.VacLoc.schrL ψ w).restrict fun _ hφ => schr_mem hψ w hφ

theorem schrS_coe (hψ : Continuous ψ) (w : (κ → k) × (κ → k)) (φ : SB (κ → k)) :
    (schrS hψ w φ : (κ → k) → ℂ) = schr ψ w φ := rfl

end Schr

section Lin

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E} {δ : E}

def trB (c : E →ₐ[k] E) : LinearMap.BilinForm k (Fin 2 → E) :=
  LinearMap.mk₂ k (fun u v => Algebra.trace k E (u 0 * c (v 1) - u 1 * c (v 0)))
    (fun u u' v => by rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun a u v => by rw [← map_smul]; congr 1; simp [smul_sub])
    (fun u v v' => by rw [← map_add]; congr 1; simp only [Pi.add_apply, map_add]; ring)
    (fun a u v => by rw [← map_smul]; congr 1; simp [smul_sub])

omit [Invertible (2 : k)] in
theorem trB_apply (u v : Fin 2 → E) : trB c u v = Algebra.trace k E (u 0 * c (v 1) - u 1 * c (v 0)) := rfl

omit [Invertible (2 : k)]

def actC (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (g : GL (Fin 2) E) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  e.toLinearMap ∘ₗ (Matrix.toLin' g.val).restrictScalars k ∘ₗ e.symm.toLinearMap

theorem actC_actC (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (g g' : GL (Fin 2) E) (x : Fin 4 → k) :
    actC e g (actC e g' x) = actC e (g * g') x := by simp [actC]

theorem actC_one (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (x : Fin 4 → k) : actC e 1 x = x := by simp [actC]

def linOm (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) :
    UG c J →* Module.End ℂ ((Fin 4 → k) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ (actC e (h : GL (Fin 2) E)⁻¹)
  map_one' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_one]
  map_mul' h h' := LinearMap.ext fun φ => funext fun x => by simp [LinearMap.funLeft, actC_actC]

theorem linOm_apply (e : (Fin 2 → E) ≃ₗ[k] (Fin 4 → k)) (J : Matrix (Fin 2) (Fin 2) E) (h : UG c J) (φ : (Fin 4 → k) → ℂ)
    (x : Fin 4 → k) : linOm e J h φ x = φ (actC e (h : GL (Fin 2) E)⁻¹ x) := rfl

end Lin

end GlobalTheory.HypPair

end
