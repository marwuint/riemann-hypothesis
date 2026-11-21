import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

abbrev EH (n : ℕ) := EuclideanSpace ℂ (Fin n)

def rsM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EH n)) :=
  ((toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A : EH n →L[ℂ] EH n) : EH n →ₗ[ℂ] EH n).restrict
    (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)

theorem rsM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : (⊤ : Submodule ℂ (EH n))) :
    ((rsM A v : (⊤ : Submodule ℂ (EH n))) : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v := rfl

end ReciprocityTheory.ChartRestriction.DS
