import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.MacdonaldWhittaker

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section CharSum

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def negCharC (ψ : AddChar F Circle) : AddChar F ℂ where
  toFun x := ((ψ (-x) : Circle) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [neg_add, AddChar.map_add_eq_mul]
    simp

theorem negCharC_apply (ψ : AddChar F Circle) (x : F) :
    negCharC ψ x = ((ψ (-x) : Circle) : ℂ) := rfl

end CharSum

end GlobalTheory.CompanionTheory.LFUDom
