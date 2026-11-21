import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

def wR : InfinitePlace ℚ := Rat.infinitePlace

theorem wR_isReal : wR.IsReal := Rat.isReal_infinitePlace

def eR : wR.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal wR_isReal

abbrev psiF (v : Pl) : AddChar (Qv v) Circle := localAdelicChar ℚ v

abbrev sph (D : Dat) (v : Pl) : GL (Fin 3) (Qv v) → ℂ := sphW (psiF v) (D.ν v)

structure Loc (D : Dat) where
  VF : ∀ v : Pl, Submodule ℂ (GL (Fin 3) (Qv v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VR : Submodule ℂ (GL (Fin 3) ℝ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VR
  hR : WhR D.k VR E

variable {D : Dat}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ) : Prop where
  inf : Wi ∈ L.VR
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset Pl, ∀ v ∉ S, Wf v = sph D v

end Ad3.GP
