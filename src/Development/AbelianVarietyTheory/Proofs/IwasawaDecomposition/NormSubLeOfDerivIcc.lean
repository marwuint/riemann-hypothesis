import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool}

theorem IsDerFam.hasDerivAt_exp {F : List (Mx n) → Mx n → ℂ} (hF : IsDerFam ε F) {l : List (Mx n)}
    (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n} (hX : X ∈ lieSet ε) {z : Mx n} (hz : z ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => F l (z * NormedSpace.exp (t • X))) (F (X :: l) (z * NormedSpace.exp (s • X))) s := by
  have h1 := hF l hl X hX _ (mul_mem_UJ hz (exp_mem_UJ hX s))
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = F l (z * _ * _)
  rw [Matrix.mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem norm_sub_le_of_deriv_Icc {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {δ B : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s ∈ Set.Icc (-δ) δ, ‖f' s‖ ≤ B) {t : ℝ} (ht : t ∈ Set.Icc (-δ) δ) : ‖f t - f 0‖ ≤ B * |t| := by
  have := (convex_Icc (-δ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hB (x := 0) (y := t) ⟨by linarith, hδ⟩ ht
  simpa using this

end GlobalTheory.TypeSum
