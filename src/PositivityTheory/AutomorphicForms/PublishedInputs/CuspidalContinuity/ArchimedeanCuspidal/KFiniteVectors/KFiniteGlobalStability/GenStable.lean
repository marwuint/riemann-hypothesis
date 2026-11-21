import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.GPK

variable {K : Type} [Field K] [NumberField K]

abbrev psiF (v : PlK K) : AddChar (Kv K v) Circle := localAdelicChar K v

abbrev sph (D : DatK K) (v : PlK K) : GL (Fin 3) (Kv K v) → ℂ := sphW (psiF v) (D.ν v)

structure Loc (D : DatK K) where
  VF : ∀ v : PlK K, Submodule ℂ (GL (Fin 3) (Kv K v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VC : Submodule ℂ (GL (Fin 3) ℂ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VC
  E' : Fin 3 → Fin 3 → Module.End ℂ VC
  hC : WhC D.k VC E E'

variable {D : DatK K}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℂ → ℂ) (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) : Prop where
  inf : Wi ∈ L.VC
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset (PlK K), ∀ v ∉ S, Wf v = sph D v

end Ad3.K.GPK
