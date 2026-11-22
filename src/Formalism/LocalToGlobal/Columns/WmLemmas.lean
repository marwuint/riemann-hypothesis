import Mathlib
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
import Formalism.LocalToGlobal.Columns.HeckeSpCount
import Formalism.LocalToGlobal.Columns.GSetLemmas

open NumberField IsDedekindDomain Module Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Nb

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (V : Type) [AddCommGroup V] [Module X.K V]

theorem trF_nbFun (a : GLG X.E n SG) (P : Ideal (𝓞 X.E)) (i : ℕ) (ψ : DecoSet X.E n ST SG → V) :
    trF X n ST SG V a (nbFun X.K V P i ψ) = nbFun X.K V P i (trF X n ST SG V a ψ) := by
  funext d
  rw [trF_apply]
  show ∑ d₁ ∈ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d).heckeNb P i, ψ d₁ =
    ∑ d₁ ∈ d.heckeNb P i, ψ ((((1 : UF X.E n), a⁻¹) : UF X.E n × GLG X.E n SG) • d₁)
  set g : UF X.E n × GLG X.E n SG := ((1 : UF X.E n), a⁻¹)
  refine Finset.sum_nbij' (fun e => g⁻¹ • e) (fun e => g • e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have : g • (g⁻¹ • e) ∈ (g • d).heckeNb P i := by rwa [smul_inv_smul]
    exact (DecoSet.smul_mem_heckeNb_iff g).1 this
  · intro e he
    exact (DecoSet.smul_mem_heckeNb_iff g).2 he
  · intro e _
    exact smul_inv_smul g e
  · intro e _
    exact inv_smul_smul g e
  · intro e _
    rw [smul_inv_smul]

end Nb

end Formalism.L2.Col
