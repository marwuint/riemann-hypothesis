import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import GroundTheory.AutomorphicForms.ReductionSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke

noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

end GlobalTheory.HenQ.Basic
