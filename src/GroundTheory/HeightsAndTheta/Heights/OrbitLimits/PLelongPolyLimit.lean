import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongPolyLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GraphIdeal
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLocalMultComap
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLelongWeightLimit

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem smoothNear_comp_init {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by
  obtain ⟨U, hU, hJU, hgU⟩ := hg
  have hinit : ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℂ => Fin.init x) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (Fin.castSucc i)
  exact ⟨(fun x => Fin.init x) ⁻¹' U, hU.preimage hinit.continuous,
    fun x hx => hJU (init_mem_zeroSet p hx), hgU.comp hinit.contDiffOn fun _ hx => hx⟩

theorem linEval_single_last {n : ℕ} (x : Fin (n + 1) → ℂ) :
    linEval (Pi.single (Fin.last n) 1) x = x (Fin.last n) := by
  simp [linEval, Pi.single_apply]

end GroundTheory.Heights₂.Heights.Targets
